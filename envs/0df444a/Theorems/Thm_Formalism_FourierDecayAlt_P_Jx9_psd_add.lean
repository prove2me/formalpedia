-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add
-- name    : Formalism.FourierDecayAlt.P.Jx9.psd_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:22.557323+00:00
-- url     : https://prove2.me/theorems/8cefe1ff-cb7a-44c4-aca3-9e2f05aa15d1
-- title:
--   Jx9: psd add
-- statement:
--   The Jx9 construction uses the psd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L21-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {α X : Type}

theorem Formalism.FourierDecayAlt.P.Jx9.psd_add {F : Finset α} {k k' : α → α → ℂ} (h : A5.IsPSD F k) (h' : A5.IsPSD F k') :
    A5.IsPSD F (fun x y => k x y + k' x y) := by sorry
