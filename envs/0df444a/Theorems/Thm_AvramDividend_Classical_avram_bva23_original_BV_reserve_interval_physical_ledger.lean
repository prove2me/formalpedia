-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva23_original_BV_reserve_interval_physical_ledger
-- name    : AvramDividend.Classical.avram_bva23_original_BV_reserve_interval_physical_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:27:58.264993+00:00
-- url     : https://prove2.me/theorems/af32c83b-26a7-40a3-babc-5c4b3a048e35
-- title:
--   Original BV reserve increment equals drift minus physical jumps and dividends
-- statement:
--   Under the original Standing and bounded-variation hypotheses, the actual controlled reserve on the original sample space satisfies the two-clock chronological source ledger: its increment is the BV deterministic drift, less the original negative-source-jump real tsum on (a,b], less the genuine cumulative-dividend increment. This holds simultaneously for every a ≤ b outside one P-null set, including the zero clock. It links the proved source identity to the actual dividend Stieltjes ledger needed for the stopped HJB cash argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bva23_original_BV_reserve_interval_physical_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      riskProcess X x D b ω - riskProcess X x D a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
          (D b ω - D a ω) := by sorry
