-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_jump_tail_integrable
-- name    : AvramDividend.Classical.avram_p4_c_generator_large_jump_tail_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:42:59.016217+00:00
-- url     : https://prove2.me/theorems/24ddbe3c-d7a3-44c2-95ca-14e7c712336f
-- title:
--   Original generator domain implies uncompensated large-jump tail integrability
-- statement:
--   GeneratorIntegrable is source integrability of the compensated remainder on (-∞,0). Restrict to (-∞,-1), then identify the uncompensated difference using the strict truncation endpoint. P2 supplies the subsequent stochastic intensity bridge.
-- source:
--   AvramDividend_Classical_SpectrallyNegativeLevy and DividendStrategy exact definitions, original paper generator at p. 20 and Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_large_jump_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y : ℝ)
    (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-1 : ℝ)) X.ν := by sorry
