-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_one
-- name    : Formalism.FourierDecayAlt.P.Jx7.psd_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:53.993091+00:00
-- url     : https://prove2.me/theorems/6bd11a1e-d8b2-486c-82d4-c7a61102e1cf
-- title:
--   Jx7: psd one
-- statement:
--   The Jx7 construction uses the psd one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L834-L842
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L834-L842

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

theorem Formalism.FourierDecayAlt.P.Jx7.psd_one : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by sorry
