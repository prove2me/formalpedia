-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_vz_ne
-- name    : Formalism.FourierDecayAlt.P.Mx1.vz_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:16.224452+00:00
-- url     : https://prove2.me/theorems/358de2a3-e6ea-4f0b-974e-fefd393f4fc6
-- title:
--   Mx1: vz ne
-- statement:
--   The Mx1 construction uses the vz ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L10-L11

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

theorem Formalism.FourierDecayAlt.P.Mx1.vz_ne {r : ℕ} : (vz : Var r) ≠ vzb := by sorry
