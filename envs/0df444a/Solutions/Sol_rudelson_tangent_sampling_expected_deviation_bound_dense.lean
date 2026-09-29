-- Prove2me | solution 1 for rudelson_tangent_sampling_expected_deviation_bound_dense
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T15:45:19.881759+00:00
-- url     : https://prove2.me/submissions/4b33fff5-c2d8-40ca-af78-b5d53e2202ab

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_rudelson_tangent_sampling_expected_deviation_core_bound_dense
import Theorems.Thm_tangent_expected_deviation_core_scale_le_beta_scale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

/-! Reduction of `rudelson_tangent_sampling_expected_deviation_bound_dense` (the corrected
    `_dense` variant of the false ancestor 2caaf179) to the corrected core node
    `rudelson_tangent_sampling_expected_deviation_core_bound_dense` (84cb7b28).

    Bridge (Proved on platform):
      - tangent_expected_deviation_core_scale_le_beta_scale (75b0243b):
        `tangentSamplingExpectedDeviationScale Ccore μ₀ n r m
           ≤ tangentSamplingDeviationScale C β μ₀ n r m`  for `2 < β`.

    The β-scale conclusion follows from the expected-deviation scale by absorbing the
    extra `√β ≥ √2` factor.  Source: Candès–Recht 2009, arXiv:0805.4471, Theorem 4.2
    eq (4.9) p.18 (expected deviation) + the final β-absorption step (§6, the
    `q = β log n` moment-window choice, pp.23–24), valid under the density side
    condition `m ≳ β μ₀ n r log n`.  The extra A1 hypothesis is not needed for the
    expected-deviation scale and is carried through unused. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m := by
  obtain ⟨Ccore, hCcore, Hcore⟩ :=
    rudelson_tangent_sampling_expected_deviation_core_bound_dense
  obtain ⟨C, hC, Hbeta⟩ :=
    tangent_expected_deviation_core_scale_le_beta_scale Ccore hCcore
  refine ⟨C, hC, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ₀ hμ₁ hA0 hA1 hdens
  -- core node → E[Z] ≤ expectedScale Ccore μ₀ max r m
  have hExp := Hcore β hβ n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hμ₀ hA0 hdens
  -- β-absorption bridge → expectedScale ≤ βScale C β μ₀ max r m
  have hBeta := Hbeta β μ₀ (max n₁ n₂) r m hβ
  exact le_trans hExp hBeta
