-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_countable
-- name    : Formalism.MainNotions.LeviCoordinates.rrd_countable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:20.932879+00:00
-- url     : https://prove2.me/theorems/eef54910-46de-45ba-bd32-c079b5f8fb30
-- title:
--   Levi Coordinates: rrd countable
-- statement:
--   The Levi Coordinates construction uses the rrd countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L10-L34

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

theorem Formalism.MainNotions.LeviCoordinates.rrd_countable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by sorry
