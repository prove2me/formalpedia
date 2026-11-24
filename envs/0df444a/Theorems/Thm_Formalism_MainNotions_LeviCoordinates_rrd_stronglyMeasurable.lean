-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_stronglyMeasurable
-- name    : Formalism.MainNotions.LeviCoordinates.rrd_stronglyMeasurable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:03.002861+00:00
-- url     : https://prove2.me/theorems/a2ec0e6f-1fc3-4fec-925d-fed861edfa04
-- title:
--   Levi Coordinates: rrd strongly Measurable
-- statement:
--   The Levi Coordinates construction uses the rrd strongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L36-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L36-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace

theorem Formalism.MainNotions.LeviCoordinates.rrd_stronglyMeasurable {α : Type*} [MeasurableSpace α] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H] (F : α → H)
    (hF : ∀ x, StronglyMeasurable fun a => ⟪x, F a⟫_ℂ) : StronglyMeasurable F := by sorry
