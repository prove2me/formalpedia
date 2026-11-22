-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_zero
-- name    : Formalism.FourierDecayAlt.P.Jx7.psd_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:57.282931+00:00
-- url     : https://prove2.me/theorems/fccda360-144d-468d-a572-3d1dca6322e2
-- title:
--   Jx7: psd zero
-- statement:
--   The Jx7 construction uses the psd zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L720-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L720-L721

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

theorem Formalism.FourierDecayAlt.P.Jx7.psd_zero : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by sorry
