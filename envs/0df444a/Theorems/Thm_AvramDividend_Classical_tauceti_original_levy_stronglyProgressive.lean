-- Prove2me | Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
-- name    : AvramDividend.Classical.tauceti_original_levy_stronglyProgressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:47:57.224945+00:00
-- url     : https://prove2.me/theorems/b4fea7ba-4e52-4001-bc27-02543bb18a4d
-- title:
--   Original spectrally negative Lévy process is strongly progressive on its given filtration
-- statement:
--   The actual adapted everywhere right-continuous spectrally negative Levy process X has a jointly strongly measurable restriction to each bounded time horizon and its contemporaneous filtration, enabling genuine stopped stochastic-process and finite-variation constructions. It follows directly from the existing fields X.adapted and X.rightCont, without assuming a completed or right-continuous filtration.
-- source:
--   Specialisation of TauCetiProject/TauCeti TauCeti/Probability/Process/Progressive.lean: MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous. Its proof uses capped right grid samples, strong measurability of countable-time sampled adapted processes, and right continuity. Apache-2.0; Copyright (c) 2026 The Tau Ceti contributors. Intended to supply the root-connected Avram stopped Ito-Meyer measurability interface, particularly 6b50f324-ce17-458d-995b-8dcff5d9e075.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set TopologicalSpace AvramDividend.Classical
open scoped NNReal Topology

theorem AvramDividend.Classical.tauceti_original_levy_stronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyProgressive 𝓕 X.X := by sorry
