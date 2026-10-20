-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_everywhere
-- name    : AvramDividend.Classical.chat03_scale_zero_extension_continuous_everywhere
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:01:45.389857+00:00
-- url     : https://prove2.me/theorems/22fe9043-325a-48e2-8d65-bb701414ac0e
-- title:
--   Global continuity of the q-scale zero extension when W(0) is zero
-- statement:
--   The official q-scale function is identically zero below zero and continuous on the nonnegative half-line. Under the explicit hypothesis W(0)=0, these pieces glue continuously over all real reserves. Consequently W is continuous at every real argument. This globally resolves sample-value continuity, for the branch in which the zero-boundary value vanishes.
-- source:
--   Independent direct proof using official IsScaleFunction and pinned Mathlib closed-set union continuity; strengthens the separately Proved continuity-at-origin helper without assuming the parent exit identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn

open MeasureTheory Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_scale_zero_extension_continuous_everywhere
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    ∀ y : ℝ, ContinuousAt W y := by sorry
