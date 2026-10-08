-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_negative_persists_right
-- name    : AvramDividend.Classical.riskProcess_negative_persists_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:55:34.499249+00:00
-- url     : https://prove2.me/theorems/7fb6e220-9eb2-4a45-9aee-5aa50b18df69
-- title:
--   Negative controlled reserves persist locally to the right
-- statement:
--   If the controlled reserve U_t=x+X_t-D_t is negative at a deterministic time t, then it remains negative for all sufficiently close later times. Right continuity of the Lévy path controls X_s-X_t, while monotonicity of cumulative dividends gives D_s≥D_t, so dividends cannot undo negativity.
-- source:
--   Pathwise measurability helper for the ruin time in the local verification theorem, Proposition 4(i) of Avram–Palmowski–Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_negative_persists_right
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hmono : ∀ ω, Monotone (fun t => D t ω))
    (ω : Ω) (t : ℝ≥0)
    (hneg : riskProcess X x D t ω < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ≥0, t ≤ s → dist s t < δ →
        riskProcess X x D s ω < 0 := by sorry
