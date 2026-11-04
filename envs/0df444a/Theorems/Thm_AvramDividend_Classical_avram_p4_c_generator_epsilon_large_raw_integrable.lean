-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_raw_integrable
-- name    : AvramDividend.Classical.avram_p4_c_generator_epsilon_large_raw_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:44:57.638504+00:00
-- url     : https://prove2.me/theorems/cfff7d26-d43f-4434-a0c2-5a46d334d8bb
-- title:
--   Original generator-integrable payoff has finite raw negative large-jump moment at every strict cutoff epsilon
-- statement:
--   For any 0<epsilon<1 and any original X.GeneratorIntegrable w y, the uncompensated payoff increment w(y+z)-w(y) is ν-integrable on all z<-epsilon. Combine the original source's already Proved uncompensated z≤-1 tail L1 theorem with P4-C's finite-annulus raw jump integrability, using exactly the disjoint measured union z≤-1 or -1<z<-epsilon. The atom z=-1 remains included. This is the honest markwise L1 input for a future original predictable compensation theorem.
-- source:
--   generatorIntegrand_large_negative_integrable d6d42ac6-8d73-463d-9224-0d3191ad7a0a and P4-C finite_band_raw_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_epsilon_large_raw_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-ε)) X.ν := by sorry
