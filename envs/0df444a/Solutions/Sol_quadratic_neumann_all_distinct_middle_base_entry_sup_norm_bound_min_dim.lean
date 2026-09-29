-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:49:57.209832+00:00
-- url     : https://prove2.me/submissions/60f6a168-dca9-478a-8f8c-0d9150f0a711

import Theorems.Thm_tangent_coordinate_kernel_bound_from_a0_min_dim
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

open MatrixCompletion

/-!
Sound `min(n₁,n₂)`-denominator entry sup-norm bound for the conditional middle
base matrix `quadraticAllDistinctMiddleBaseMatrix` of the triple-decoupled
all-distinct quadratic Neumann term.  Each entry is `G_{ω₂}` (bounded by
`innerBound` on the inner-coefficient event) times one tangent-coordinate kernel
`⟪P_T(eᵢeⱼᵀ), e_{w₁}⟫ ≤ Cker·μ₀·(r/min)` (A0).

Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular kernel
convention after eqs (6.2)--(6.4).  Sound `min`-denominator analogue of the
Disproved max-form supplier.
-/

private lemma mid_entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

/-- Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular
`min(n₁,n₂)` kernel convention after eqs (6.2)--(6.4). -/
theorem solution :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Centry * innerBound * μ₀ *
              ((r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with
    ⟨Cker, hCker, hKernel⟩
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound hib hInner w1
  refine mid_entrySupNorm_le_of_forall_abs_le hn₁ hn₂
    (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
    (Cker * innerBound * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) ?_
  intro i j
  by_cases hsame : (i, j) = w1
  · simp [quadraticAllDistinctMiddleBaseMatrix, hsame]
    positivity
  · have hcoeff :
        |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| ≤
          innerBound := hInner w1 (i, j)
    have hKer :=
      hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j w1.1 w1.2
    have hKer_nonneg :
        0 ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      positivity
    calc
      |quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1 i j|
          = |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| *
              |tangentCoordinateKernel S i j w1.1 w1.2| := by
            simp [quadraticAllDistinctMiddleBaseMatrix, hsame, abs_mul]
      _ ≤ innerBound * (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
          exact mul_le_mul hcoeff hKer (abs_nonneg _) hib
      _ = Cker * innerBound * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
          ring
