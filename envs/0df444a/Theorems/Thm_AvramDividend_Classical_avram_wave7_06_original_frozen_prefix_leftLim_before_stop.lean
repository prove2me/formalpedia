-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
-- name    : AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_leftLim_before_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:27:50.078599+00:00
-- url     : https://prove2.me/theorems/8e873bf7-80af-4a6c-9481-138838e7645b
-- title:
--   Original spectrally negative Lévy frozen-prefix left limits coincide through the stop horizon
-- statement:
--   For any actual original Lévy path and any time 0<u≤T, freezing the path at T preserves the strict-left limit at u, including u=T. This source-exact prefix locality supports transferring original marked jump events to measurable frozen-prefix functionals in the raw filtration.
-- source:
--   W7-06 original small-jump compensated L²/L¹ martingale, pinned Mathlib 0df444a, source X.leftLim axiom and strict-left filter eventual equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_leftLim_before_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T u : ℝ≥0) (hu : 0 < u) (huT : u ≤ T) :
    Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u =
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by sorry
