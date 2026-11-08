-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_uniform_two_index_positive_endpoint_prestate
-- name    : AvramDividend.Classical.avram_bv_stieltjes10_original_uniform_two_index_positive_endpoint_prestate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:58:15.699039+00:00
-- url     : https://prove2.me/theorems/6280b6fa-9d6e-4e4c-a72c-751ee7125813
-- title:
--   Original prepayment reserve at all positive uniform physical-cell endpoints
-- statement:
--   For the literal deterministic uniform physical grid used in the original positive-horizon BV source, prove a single almost-sure identity over both mesh resolution and positive cell endpoint indices, equating the post-rightpayment path left limit with the actual prepayment reserve. This exactly supplies the hPre premise of the finite-cap original two-scale row-certificate theorem e6a0b83b, without adding stochastic hypotheses.
-- source:
--   Public Proved e26f2e74 countable positive prepayment grid; IsAdmissibleLe projects to IsDividendStrategy by hD.1.1; positive deterministic uniform u n (i+1) from T>0 and exact grid coordinate formula.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_stieltjes10_original_uniform_two_index_positive_endpoint_prestate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by sorry
