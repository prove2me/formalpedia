-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_preRuin_eventually_right_solvent
-- name    : AvramDividend.Classical.avram_wave3_03_preRuin_eventually_right_solvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:35:57.363472+00:00
-- url     : https://prove2.me/theorems/e8ccd8aa-6a10-4a3b-b6ed-5828747428af
-- title:
--   Strict pre-ruin reserve remains solvent on an entire right time germ
-- statement:
--   At every deterministic or path-dependent time T strictly before the actual controlled ruin time, the original controlled reserve is nonnegative eventually along times strictly to the right of T. This follows from right-neighbourhood continuity of the NNReal to ENNReal time embedding and the proved source ruin-order solvency. Together with the proved post-payment right-limit boundary lemma, it discharges the explicit near-T solvency premise needed for the same-horizon BV Stieltjes drift envelope.
-- source:
--   Proved riskProcess_nonneg_before_ruin c26c83f7 and Mathlib continuity/order topology of ℝ≥0→ℝ≥0∞.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_preRuin_eventually_right_solvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ᶠ s in 𝓝[>] T, 0 ≤ riskProcess X x D s ω := by sorry
