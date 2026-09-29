-- Prove2me | solution 1 for talagrand_tangent_sampling_supremum_absolute_deviation_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:30.52776+00:00
-- url     : https://prove2.me/submissions/5b700854-fcba-4f8d-a36a-4a2bdbe3131f

import Theorems.Thm_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
import Definitions.Def_matrix_completion_talagrand_supremum

open MatrixCompletion
open scoped Classical BigOperators

/-!
Source: Candes--Recht, Appendix 9.1, PDF p. 46, equations (9.1)--(9.2).

This reduction instantiates the exact logarithmic Talagrand product-space
theorem with the Appendix 9.1 bilinear coefficient
`tangentSamplingTalagrandCoefficient S p X₁ X₂ i j`.  Unlike the deprecated
raw-tail route, the logarithmic exponent from Theorem 9.1 is preserved.
-/
theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) sigmaSq →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |tangentSamplingTalagrandSupremumDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingTalagrandSupremumDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                          (fun Omega' =>
                            tangentSamplingTalagrandSupremumDeviation Omega' S
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))))) := by
  rcases talagrand_bernoulli_supremum_centered_coordinate_process_log_tail with
    ⟨K, hK, hTalagrand⟩
  refine ⟨K, hK, ?_⟩
  intro n₁ n₂ r m M S B sigmaSq t hn₁ hn₂ _hr hm hB hsigma ht hIncrement hVariance
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let ι : Type :=
    {X : Matrix (Fin n₁) (Fin n₂) ℝ × Matrix (Fin n₁) (Fin n₂) ℝ //
      frobeniusNorm X.1 ≤ 1 ∧ frobeniusNorm X.2 ≤ 1}
  let coeff : ι → Fin n₁ → Fin n₂ → ℝ :=
    fun X i j => tangentSamplingTalagrandCoefficient S p X.1.1 X.1.2 i j
  let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => tangentSamplingTalagrandSupremumDeviation Omega S p
  have hZ :
      ∀ Omega,
        Z Omega =
          sSup {v : ℝ |
            ∃ a : ι,
              v =
                ∑ i : Fin n₁, ∑ j : Fin n₂,
                  (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                    coeff a i j)} := by
    intro Omega
    unfold Z tangentSamplingTalagrandSupremumDeviation
    congr 1
    ext v
    constructor
    · intro hv
      rcases hv with ⟨X1, X2, hX1, hX2, hv⟩
      refine ⟨⟨(X1, X2), hX1, hX2⟩, ?_⟩
      simpa [coeff] using hv
    · intro hv
      rcases hv with ⟨X, hv⟩
      refine ⟨X.1.1, X.1.2, X.2.1, X.2.2, ?_⟩
      simpa [coeff] using hv
  have hCoeffBound :
      ∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B := by
    intro X i j
    exact hIncrement X.1.1 X.1.2 X.2.1 X.2.2 i j
  have hSymmetric :
      ∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
        coeff a' i j = -coeff a i j := by
    intro X
    refine ⟨⟨(-X.1.1, X.1.2), ?_, X.2.2⟩, ?_⟩
    · simpa [frobeniusNorm, frobeniusNormSq] using X.2.1
    · intro i j
      simp [coeff, tangentSamplingTalagrandCoefficient, matrixInner]
  have hVarianceBound :
      ∀ a : ι,
        ∑ i : Fin n₁, ∑ j : Fin n₂,
          p * (1 - p) * (coeff a i j) ^ 2 ≤ sigmaSq := by
    intro X
    simpa [coeff, p] using hVariance X.1.1 X.1.2 X.2.1 X.2.2
  simpa [p, Z] using
    hTalagrand n₁ n₂ m ι Z coeff B sigmaSq t hn₁ hn₂ hm hB hsigma ht
      (by simpa [p] using hZ) hSymmetric hCoeffBound hVarianceBound
