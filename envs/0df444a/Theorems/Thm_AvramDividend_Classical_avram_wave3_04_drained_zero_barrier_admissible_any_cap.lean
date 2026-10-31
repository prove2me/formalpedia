-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drained_zero_barrier_admissible_any_cap
-- name    : AvramDividend.Classical.avram_wave3_04_drained_zero_barrier_admissible_any_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:35:00.30574+00:00
-- url     : https://prove2.me/theorems/235540e5-fcdc-4a54-b5e4-d9f443b2b815
-- title:
--   Zero-barrier plus linear drain satisfies every finite reserve cap
-- statement:
--   For any spectrally negative Lévy process, nonnegative initial capital and cap C including finite C, the zero-barrier dividend strategy plus unit continuous drain is an admissible strategy capped at C. The reserve is strictly negative at every positive time and ENNReal.ofReal of that reserve is zero. This accepted-source phenomenon is central to diagnosing the absent w(0) nonnegativity assumption in canonical unbounded-variation verification.
-- source:
--   Prove2Me source definitions IsAdmissibleLe and riskProcess; remotely Proved lemmas drained_zero_barrier_admissible_infinite_cap 98aedb39-b4a1-472b-ae28-529c4b79b233 and barrierStrategy_plus_linear_drain_reserve_negative 50cad288-014a-4651-9e48-c4391df764dc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_drained_zero_barrier_admissible_any_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) :
    IsAdmissibleLe X x C
      (fun t ω => barrierStrategy X x 0 t ω + (t : ℝ)) := by sorry
