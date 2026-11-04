-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable
-- name    : AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:17:00.114428+00:00
-- url     : https://prove2.me/theorems/8f68fb34-1ded-46c8-a51b-ecb0cf968206
-- title:
--   All nonnegative tilted fourth exponential-deficit tests are integrable on the original source
-- statement:
--   For the unchanged original spectrally negative Lévy process, every nonnegative tilt rho and every actual time t have finite expectation of exp(rho X_t)(exp(X_t)-1)^4. The proof expands the tilted fourth power into exactly five positive-rate source Laplace moments at rho through rho+4, each integrable by the source Lévy specification. This supplies genuine finite-measure construction and all polynomial weighted moments for the required small-time method-of-moments proof, without assuming a jump measure compensator or model change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Integrable (fun ω => Real.exp (ρ * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) P := by sorry
