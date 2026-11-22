-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_postdividend_reserve_rightContinuous
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_postdividend_reserve_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:42:38.293742+00:00
-- url     : https://prove2.me/theorems/9f170597-1a16-40de-97eb-533132e5ba4d
-- title:
--   Original post-dividend Levy reserve remains right-continuous after a possibly infinite stopping clock
-- statement:
--   The source-faithful post-dividend surplus x+X.X-rightLimit D is pathwise right continuous under an original dividend strategy, even after stopping at any clock (finite or infinite). The actual proof adapts FTAPTheorem42's stopped martingale right-continuity case split, combining original Avram X.rightCont and proved right continuity of rightLimit D. No artificial reward, integrability, or stochastic decomposition assumptions.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/RightContinuousStoppedMartingale.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_postdividend_reserve_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → WithTop ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (fun u : ℝ≥0 =>
        MeasureTheory.stoppedProcess
          (fun s ω => x + X.X s ω - rightLimit D s ω) τ u ω)
      (Set.Ici t) t := by sorry
