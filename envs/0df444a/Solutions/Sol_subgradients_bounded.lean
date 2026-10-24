-- Prove2me | solution 1 for subgradients_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:21:36.594749+00:00
-- url     : https://prove2.me/submissions/8c40f1ae-e266-46e2-a509-430dc46f255a

import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

/-!
The elementary enlarged-ball argument below is reused from the publicly accepted
Prove2Me proof of Shor Theorem 2.11 (submission
`5f348b7b-6f60-4214-b981-56f44bf5438d` by Nickrobbins95, target
`1718cc07-0242-4a18-953f-16c107596744`). Its original source is preserved in
`verification/night-2026-10-23/root-accepted-source.json`.
Public platform contributions are under Apache 2.0.
-/

namespace SubgradientsBoundedProof

/-- Subgradients of a function bounded by `C` on `closedBall y (R+1)` at points of
`closedBall y R` have norm at most `2C`. -/
private lemma subgrad_bound_of_function_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (y z v : EuclideanSpace ℝ (Fin n))
    (R C : ℝ) (hC : ∀ w ∈ Metric.closedBall y (R + 1), ‖f w‖ ≤ C)
    (hz : z ∈ Metric.closedBall y R) (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f z v) :
    ‖v‖ ≤ 2 * C := by
  have hR : 0 ≤ R := le_trans dist_nonneg hz
  have hzC := hC z (Metric.closedBall_subset_closedBall (by linarith) hz)
  by_cases h0 : v = 0
  · rw [h0, norm_zero]
    have := norm_nonneg (f z)
    linarith
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h0
  set w := z + (1 / ‖v‖) • v with hw
  have hwB : w ∈ Metric.closedBall y (R + 1) := by
    rw [Metric.mem_closedBall] at hz ⊢
    rw [dist_eq_norm] at hz ⊢
    have : w - y = (z - y) + (1 / ‖v‖) • v := by rw [hw]; abel
    rw [this]
    calc ‖(z - y) + (1 / ‖v‖) • v‖ ≤ ‖z - y‖ + ‖(1 / ‖v‖) • v‖ := norm_add_le _ _
      _ = ‖z - y‖ + 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
      _ ≤ R + 1 := by linarith
  have hwC := hC w hwB
  have h1 := hv w
  have : w - z = (1 / ‖v‖) • v := by rw [hw]; abel
  rw [this, inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : 1 / ‖v‖ * ‖v‖ ^ 2 = ‖v‖ := by field_simp
  rw [h2] at h1
  have a1 := abs_le.mp (Real.norm_eq_abs (f w) ▸ hwC)
  have a2 := abs_le.mp (Real.norm_eq_abs (f z) ▸ hzC)
  linarith [a1.1, a1.2, a2.1, a2.2]


/-- All subgradients of a globally finite convex function are uniformly bounded
on each closed ball in finite-dimensional Euclidean space. -/
private theorem subgradients_bounded_on_closedBall {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xm : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ Metric.closedBall xm R,
      ∀ v, ShorNonsmooth.AlmostDiff.IsSubgradient f z v → ‖v‖ ≤ B := by
  have hfc : Continuous f := hf.locallyLipschitz.continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall xm (R + 1)).exists_bound_of_continuousOn
    hfc.continuousOn
  refine ⟨max (2 * C) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz v hv
  exact (subgrad_bound_of_function_bound f xm z v R C hC hz hv).trans
    (le_max_left _ _)


end SubgradientsBoundedProof

theorem solution {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S, ∀ v,
      ShorNonsmooth.AlmostDiff.IsSubgradient f x v → ‖v‖ ≤ K := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨K, hK, hb⟩ := SubgradientsBoundedProof.subgradients_bounded_on_closedBall f hf 0 R
  exact ⟨K, hK, fun x hx v hv => hb x (hR hx) v hv⟩
