-- Prove2me | solution 1 for rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T03:29:38.8877+00:00
-- url     : https://prove2.me/submissions/47301837-62e7-43fa-a0c6-6455e81d7c5c

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Ring.Basic

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

namespace ProveSym

/-- `spectralNorm` triangle inequality on a difference. -/
theorem spectralNorm_sub_le {n1 n2 : ℕ} (A B : RealMatrix n1 n2) :
    spectralNorm (A - B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show Matrix.toEuclideanLin (A - B)
      = Matrix.toEuclideanLin A - Matrix.toEuclideanLin B from by simp [map_sub], map_sub]
  exact norm_sub_le _ _

theorem spectralNorm_nonneg {n1 n2 : ℕ} (A : RealMatrix n1 n2) : 0 ≤ spectralNorm A :=
  norm_nonneg _

/-- Bernoulli weights sum to one (witness coordinate needed). -/
theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) (w0 : Fin n1 × Fin n2) :
    ∑ Omega : Finset (Fin n1 × Fin n2), bernoulliObservationWeight p Omega = 1 := by
  have h := bernoulli_powerset_expectation_single_coordinate (n₁ := n1) (n₂ := n2) p
    w0 (fun _ => (1:ℝ))
  simpa [bernoulliExpectation] using h

theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n1 × Fin n2)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

theorem radWeight_nonneg {n1 n2 : ℕ} (eps : Finset (Fin n1 × Fin n2)) :
    0 ≤ rademacherObservationWeight eps := by
  unfold rademacherObservationWeight; positivity

end ProveSym

open ProveSym in
/-- `rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio`.
Triangle/symmetrization with constant `Csym = 2`:
`E_{Ω,Ω'} E_ε ‖A(Ω,ε)−A(Ω',ε)‖^q ≤ 2^q · E_Ω E_ε ‖A(Ω,ε)‖^q`.
Proof = pointwise `‖A−B‖^q ≤ 2^{q-1}(‖A‖^q+‖B‖^q)` (operator-norm triangle +
`add_pow_le`), monotone+linear under the nonneg `E_ε`/`E_pair` weights (needs
`p = m/(n₁n₂) ≤ 1`, the `m ≤ n₁n₂` guard), then marginalize the pair measure
(`∑ w = 1`).  Source: Candès–Recht 2009/2012, §6.1 (symmetrization, `Csym = 2`). -/
theorem solution :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega Omega' =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                      rademacherSampledMatrix Omega' eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    have : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
    linarith
  have hqne : q ≠ 0 := by omega
  set w0 : Fin n₁ × Fin n₂ := (⟨0, hn₁⟩, ⟨0, hn₂⟩) with hw0
  -- A Ω ε = rademacherSampledMatrix Ω ε p X
  set A : Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂ :=
    fun Ω eps => rademacherSampledMatrix Ω eps p X with hA
  -- h Ω = E_ε ‖A Ω ε‖^q  (the single-sample inner expectation)
  set h : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Ω => rademacherExpectation (fun eps => spectralNorm (A Ω eps) ^ q) with hh
  have hh_nn : ∀ Ω, 0 ≤ h Ω := by
    intro Ω; rw [hh]; unfold rademacherExpectation
    apply Finset.sum_nonneg; intro eps _
    exact mul_nonneg (radWeight_nonneg eps) (pow_nonneg (spectralNorm_nonneg _) q)
  -- STEP 1 (pointwise, per (Ω,Ω',ε)):
  --   ‖A Ω ε - A Ω' ε‖^q ≤ 2^{q-1}(‖A Ω ε‖^q + ‖A Ω' ε‖^q)
  have hpoint : ∀ Ω Ω' eps,
      spectralNorm (A Ω eps - A Ω' eps) ^ q ≤
        2 ^ (q - 1) * (spectralNorm (A Ω eps) ^ q + spectralNorm (A Ω' eps) ^ q) := by
    intro Ω Ω' eps
    calc spectralNorm (A Ω eps - A Ω' eps) ^ q
        ≤ (spectralNorm (A Ω eps) + spectralNorm (A Ω' eps)) ^ q :=
          pow_le_pow_left₀ (spectralNorm_nonneg _) (spectralNorm_sub_le _ _) q
      _ ≤ 2 ^ (q - 1) * (spectralNorm (A Ω eps) ^ q + spectralNorm (A Ω' eps) ^ q) :=
          add_pow_le (spectralNorm_nonneg _) (spectralNorm_nonneg _) q
  -- STEP 2: average over ε.  E_ε[‖A Ω ε - A Ω' ε‖^q] ≤ 2^{q-1}(h Ω + h Ω').
  have heps : ∀ Ω Ω',
      rademacherExpectation (fun eps => spectralNorm (A Ω eps - A Ω' eps) ^ q) ≤
        2 ^ (q - 1) * (h Ω + h Ω') := by
    intro Ω Ω'
    have hsum : rademacherExpectation (fun eps => spectralNorm (A Ω eps - A Ω' eps) ^ q) ≤
        rademacherExpectation
          (fun eps => 2 ^ (q - 1) * (spectralNorm (A Ω eps) ^ q + spectralNorm (A Ω' eps) ^ q)) := by
      unfold rademacherExpectation
      apply Finset.sum_le_sum
      intro eps _
      exact mul_le_mul_of_nonneg_left (hpoint Ω Ω' eps) (radWeight_nonneg eps)
    -- the RHS rademacherExpectation factors as 2^{q-1}*(h Ω + h Ω')
    have hfactor : rademacherExpectation
          (fun eps => 2 ^ (q - 1) * (spectralNorm (A Ω eps) ^ q + spectralNorm (A Ω' eps) ^ q))
        = 2 ^ (q - 1) * (h Ω + h Ω') := by
      simp only [hh]
      unfold rademacherExpectation
      simp only []
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro eps _; ring
    linarith [hsum, hfactor.le, hfactor.ge]
  -- STEP 3:  E_pair[E_ε ...] ≤ E_pair[2^{q-1}(h Ω + h Ω')]
  --        = 2^{q-1}( E_Ω[h Ω] + E_Ω'[h Ω'] ) = 2^{q-1}·2·E_Ω[h] = 2^q E_Ω[h].
  have hweights1 : ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω = 1 :=
    weights_sum_one p w0
  -- bound the pair expectation termwise
  have hpairle : bernoulliPairExpectation p
        (fun Ω Ω' => rademacherExpectation (fun eps => spectralNorm (A Ω eps - A Ω' eps) ^ q)) ≤
      bernoulliPairExpectation p (fun Ω Ω' => 2 ^ (q - 1) * (h Ω + h Ω')) := by
    unfold bernoulliPairExpectation
    apply Finset.sum_le_sum; intro Ω _
    apply Finset.sum_le_sum; intro Ω' _
    apply mul_le_mul_of_nonneg_left (heps Ω Ω')
    exact mul_nonneg (weight_nonneg hp0 hp1 Ω) (weight_nonneg hp0 hp1 Ω')
  -- evaluate the RHS pair expectation in closed form
  have hpaireval : bernoulliPairExpectation p (fun Ω Ω' => 2 ^ (q - 1) * (h Ω + h Ω'))
      = 2 ^ q * bernoulliExpectation p h := by
    have hEh : bernoulliExpectation p h
        = ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω * h Ω := by
      rw [bernoulliExpectation]
    -- term1 = ∑_Ω ∑_Ω' w_Ω w_Ω' h_Ω   = E[h]
    have hterm1 : ∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ Ω' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' * h Ω
        = bernoulliExpectation p h := by
      rw [hEh]
      apply Finset.sum_congr rfl; intro Ω _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [show (∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω') = 1 from hweights1]
      ring
    -- term2 = ∑_Ω ∑_Ω' w_Ω w_Ω' h_Ω'   = E[h]
    have hterm2 : ∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ Ω' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' * h Ω'
        = bernoulliExpectation p h := by
      rw [hEh, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro Ω' _
      rw [← Finset.sum_mul]
      rw [show (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω
            * bernoulliObservationWeight p Ω') =
          (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω)
            * bernoulliObservationWeight p Ω' from by rw [Finset.sum_mul]]
      rw [hweights1]; ring
    unfold bernoulliPairExpectation
    have hsplit : ∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ Ω' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            (2 ^ (q - 1) * (h Ω + h Ω'))
        = 2 ^ (q - 1) *
            ((∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ Ω' : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' * h Ω)
            + (∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ Ω' : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' * h Ω')) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro Ω _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro Ω' _; ring
    rw [hsplit, hterm1, hterm2]
    rw [show (2:ℝ) ^ q = 2 ^ (q - 1) * 2 from by
          rw [← pow_succ]; congr 1; omega]
    ring
  calc bernoulliPairExpectation p
        (fun Ω Ω' => rademacherExpectation (fun eps => spectralNorm (A Ω eps - A Ω' eps) ^ q))
      ≤ bernoulliPairExpectation p (fun Ω Ω' => 2 ^ (q - 1) * (h Ω + h Ω')) := hpairle
    _ = 2 ^ q * bernoulliExpectation p h := hpaireval
