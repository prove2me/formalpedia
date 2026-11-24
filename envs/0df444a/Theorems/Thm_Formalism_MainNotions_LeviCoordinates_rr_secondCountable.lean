-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_secondCountable
-- name    : Formalism.MainNotions.LeviCoordinates.rr_secondCountable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:46.826272+00:00
-- url     : https://prove2.me/theorems/e029380e-8b2b-4baa-b3f6-40c5efbaada8
-- title:
--   Levi Coordinates: rr second Countable
-- statement:
--   The Levi Coordinates construction uses the rr second Countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrsSecondCountableAbs.lean#L85-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrsSecondCountableAbs.lean#L85-L98

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
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
open MeasureTheory Set Topology
open scoped Pointwise
open Formalism.MainNotions.S

theorem Formalism.MainNotions.LeviCoordinates.rr_secondCountable (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    SecondCountableTopology I.Gf := by sorry
