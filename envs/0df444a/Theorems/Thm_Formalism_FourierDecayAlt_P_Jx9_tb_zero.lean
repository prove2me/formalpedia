-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_tb_zero
-- name    : Formalism.FourierDecayAlt.P.Jx9.tb_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.304219+00:00
-- url     : https://prove2.me/theorems/eed2ce15-a554-4f6c-807a-78ec66ad4678
-- title:
--   Jx9: tb zero
-- statement:
--   The Jx9 construction uses the tb zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L128-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L128-L129

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

theorem Formalism.FourierDecayAlt.P.Jx9.tb_zero {α : Type} {F : Finset α} : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by sorry
