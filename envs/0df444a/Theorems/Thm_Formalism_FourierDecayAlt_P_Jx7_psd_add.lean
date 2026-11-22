-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add
-- name    : Formalism.FourierDecayAlt.P.Jx7.psd_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:42.659983+00:00
-- url     : https://prove2.me/theorems/cd6c85a3-1c22-42f6-90fa-e8e47cdced66
-- title:
--   Jx7: psd add
-- statement:
--   The Jx7 construction uses the psd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L723-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L723-L726

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
variable {α : Type} {F : Finset α}

theorem Formalism.FourierDecayAlt.P.Jx7.psd_add {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y + k' x y) := by sorry
