-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_stopped_gaussian_exact_energy_isometry
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_exact_energy_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:05:31.076801+00:00
-- url     : https://prove2.me/theorems/0440d0f9-46cc-4656-acd6-9b88f043a955
-- title:
--   Original zero-jump Levy Gaussian martingale has exact expected stopped energy sigma squared times the stopped clock
-- statement:
--   For the actual zero-jump original spectrally negative Levy process X and a genuine bounded countable-range stopping time τ in the original right-continuous filtration, its centred Gaussian process M_t=X_t-tc has square-integrable stopped value and satisfies exact expected square E[M_τ²]=σ²E[τ], with the clock interpreted as WithTop.untopA. Integrability of the stopped compensator is a conclusion. All inputs are already proven true original martingales and the LSV exact stopped isometry; no synthetic source or unproved Brownian representation is assumed. Lean-LSV CC BY 4.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_quadratic_energy_isometry

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Exact original-process stopped Gaussian isometry from the true quadratic
martingale and the stopped energy lemma adapted from dufeteller/lean-lsv,
LSV/LocalizedStoppingL2Convergence.lean and LocalizedOptionalExpectation.lean,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719, CC BY 4.0.
-/

theorem AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_exact_energy_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun s ω => X.X s ω - (s : ℝ) * X.c
    Integrable (fun ω => ((τ ω).untopA : ℝ) * X.σ^2) P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
        ∫ ω, ((τ ω).untopA : ℝ) * X.σ^2 ∂P := by sorry
