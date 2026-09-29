-- Prove2me | solution 1 for entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T12:38:30.923677+00:00
-- url     : https://prove2.me/submissions/455ca019-b1a4-4f17-9c50-54d2bdda5a72

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

/-- G1: `|E_ij| ≤ μ₀ r / √(n₁ n₂)` from A0 by Cauchy–Schwarz. -/
theorem solution :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
      entrySupNorm (signMatrix S) ≤
        μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  -- coordinate energy bounds from A0
  have energy_le :
      ∀ (N : ℕ) (w : Fin r → Fin N → ℝ),
        0 < N →
        (N : ℝ) / (r : ℝ) * (⨆ i : Fin N, ∑ k, (w k i) ^ 2) ≤ μ₀ →
        ∀ hNe : Nonempty (Fin N),
        ∀ i : Fin N, ∑ k, (w k i) ^ 2 ≤ μ₀ * (r : ℝ) / (N : ℝ) := by
    intro N w hN hcoh hNe i
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hbdd : BddAbove (Set.range fun i : Fin N => ∑ k, (w k i) ^ 2) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hle : (∑ k, (w k i) ^ 2) ≤ ⨆ i : Fin N, ∑ k, (w k i) ^ 2 :=
      le_ciSup hbdd i
    have hpos : (0 : ℝ) < (N : ℝ) / (r : ℝ) := div_pos hNR hrR
    have hcoh' : (⨆ i : Fin N, ∑ k, (w k i) ^ 2) * ((N : ℝ) / (r : ℝ)) ≤ μ₀ := by
      calc (⨆ i : Fin N, ∑ k, (w k i) ^ 2) * ((N : ℝ) / (r : ℝ))
          = (N : ℝ) / (r : ℝ) * ⨆ i : Fin N, ∑ k, (w k i) ^ 2 := by ring
        _ ≤ μ₀ := hcoh
    have h2 := (le_div_iff₀ hpos).mpr hcoh'
    refine hle.trans (h2.trans_eq ?_)
    field_simp
  have hU := energy_le n₁ S.u hn₁ hA0.1 ‹Nonempty (Fin n₁)›
  have hV := energy_le n₂ S.v hn₂ hA0.2 ‹Nonempty (Fin n₂)›
  -- entrywise Cauchy–Schwarz bound
  have hentry : ∀ (i : Fin n₁) (j : Fin n₂),
      |signMatrix S i j| ≤ μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by
    intro i j
    have hE : signMatrix S i j = ∑ k, S.u k i * S.v k j := by
      unfold signMatrix
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
    have hCS : (∑ k, S.u k i * S.v k j) ^ 2 ≤
        (∑ k, (S.u k i) ^ 2) * ∑ k, (S.v k j) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    have hsum_u_nonneg : (0 : ℝ) ≤ ∑ k, (S.u k i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsum_v_nonneg : (0 : ℝ) ≤ ∑ k, (S.v k j) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hprod : (∑ k, (S.u k i) ^ 2) * (∑ k, (S.v k j) ^ 2) ≤
        (μ₀ * (r : ℝ) / (n₁ : ℝ)) * (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      have hb : (0 : ℝ) ≤ μ₀ * (r : ℝ) / (n₁ : ℝ) := by positivity
      exact mul_le_mul (hU i) (hV j) hsum_v_nonneg hb
    have hsq : (signMatrix S i j) ^ 2 ≤ (μ₀ * (r : ℝ)) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)) := by
      rw [hE]
      refine (hCS.trans hprod).trans_eq ?_
      field_simp
      try ring
    have habs : |signMatrix S i j| = Real.sqrt ((signMatrix S i j) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    rw [habs]
    have := Real.sqrt_le_sqrt hsq
    refine this.trans_eq ?_
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
  -- assemble the double supremum
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => hentry i j
