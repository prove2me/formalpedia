-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_psd_mul
-- name    : Formalism.FourierDecayAlt.P.Jx6.psd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:51.454182+00:00
-- url     : https://prove2.me/theorems/72f6bf18-8c81-4e9e-8e1e-c313634705f9
-- title:
--   Jx6: psd mul
-- statement:
--   The Jx6 construction uses the psd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L8-L11

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6

theorem Formalism.FourierDecayAlt.P.Jx6.psd_mul {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : TB.PSDOn F (fun x y => k x y * k' x y) := by sorry
