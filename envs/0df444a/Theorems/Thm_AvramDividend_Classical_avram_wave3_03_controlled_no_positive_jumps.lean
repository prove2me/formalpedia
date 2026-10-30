-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_controlled_no_positive_jumps
-- name    : AvramDividend.Classical.avram_wave3_03_controlled_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:02:30.10706+00:00
-- url     : https://prove2.me/theorems/df7b5f2d-5cfb-4281-afd4-96a74bf17f5f
-- title:
--   Admissible controlled reserve inherits no positive left jumps
-- statement:
--   For any actual dividend strategy adapted and left-continuous in time, the controlled reserve has no positive jump from the left at any strictly positive time, regardless of bounded or unbounded variation. The inherited limit is evaluated after the underlying Lévy jump and before a possible right dividend jump. This is a source-specific boundary property for stopped ruin localisation.
-- source:
--   Exact SpectrallyNegativeLevy.noPosJumps and IsDividendStrategy left-continuity source fields. A controlled reserve has left limit l; adding the left-continuous dividend D and subtracting initial x produces the Lévy left limit. The Lévy no-positive-jump inequality transfers algebraically. This isolates a positive-time boundary property needed by BV stochastic verification, without assuming Stieltjes mass concentration or the stochastic bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set
open AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave3_03_controlled_no_positive_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (l : ℝ)
    (hl : Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω) (𝓝[<] t) (𝓝 l)) :
    riskProcess X x D t ω ≤ l := by sorry
