-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_euler_support
-- name    : Formalism.FourierDecayAlt.P.Mx1.euler_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:10.432694+00:00
-- url     : https://prove2.me/theorems/a7ab4927-0761-4896-942e-619fcf435aac
-- title:
--   Mx1: euler support
-- statement:
--   The Mx1 construction uses the euler support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L13-L19

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx1

theorem Formalism.FourierDecayAlt.P.Mx1.euler_support {r : ℕ} (v : Var r) (f : Fn r) : (euler v f).support ⊆ f.support := by sorry
