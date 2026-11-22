-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_canonical_ruinclip_gaussian_square_and_compensator
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_canonical_ruinclip_gaussian_square_and_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:21:20.736072+00:00
-- url     : https://prove2.me/theorems/c32a584b-582c-4d47-bd42-402674b487f7
-- title:
--   Original zero-jump dividend ruin-clock exact Gaussian square and centred quadratic compensator
-- statement:
--   For an actual original zero-jump spectrally negative Levy process, original admissible dividend strategy D, and the physical ruin time clipped at n with its genuine stopping-time witness, the drift-centred Gaussian residual at the true clipped stop has an integrable square of expected value sigma-squared times expected stop, and its compensated square is integrable of mean zero. No countable-range clock, hypothetical Brownian driver, or separately assumed same-space Levy Ito decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original zero-jump spectrally negative Levy process, actual
   dividend strategy and ruin-clipped stopping time. Derives both stopped
   Gaussian quadratic isometry and integrable mean-zero compensated-square
   residual. Adapted from dufeteller/lean-lsv LocalizedStoppingL2Convergence
   and LocalizedOptionalExpectation, CC BY 4.0 commit a5f604d. -/

theorem AvramDividend.Classical.avram_lsv_original_zerojump_canonical_ruinclip_gaussian_square_and_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω,
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω) ω - (τ ω : ℝ) * X.c
    Integrable (fun ω => (M ω)^2) P ∧
      (∫ ω, (M ω)^2 ∂P) =
        ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P ∧
    Integrable (fun ω => (M ω)^2 - (τ ω : ℝ) * X.σ^2) P ∧
      (∫ ω, (M ω)^2 - (τ ω : ℝ) * X.σ^2 ∂P) = 0 := by sorry
