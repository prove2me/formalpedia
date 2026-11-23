-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_map_mulVec_volume
-- name    : Formalism.FourierDecayAlt.P.G5.map_mulVec_volume
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.585919+00:00
-- url     : https://prove2.me/theorems/d695ef78-3f9b-4341-9d36-529815a531df
-- title:
--   G5: map mul Vec volume
-- statement:
--   The G5 construction uses the map mul Vec volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L23-L32

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

theorem Formalism.FourierDecayAlt.P.G5.map_mulVec_volume {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by sorry
