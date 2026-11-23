-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_add_const
-- name    : Formalism.FourierDecayAlt.P.G5.mp_add_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:44.838041+00:00
-- url     : https://prove2.me/theorems/e5000a4b-1a89-4dd2-be0c-360de46dba5a
-- title:
--   G5: mp add const
-- statement:
--   The G5 construction uses the mp add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L45-L48

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.mp_add_const (β : ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) :
    MeasurePreserving (fun x : ι → ℂ => x + c) (muPi β ι) (muPi β ι) := by sorry
