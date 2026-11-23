-- Prove2me | Theorems.Thm_Formalism_UG_P_standard_action_mul_holds
-- name    : Formalism.UG.P.standard_action_mul_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:14.341966+00:00
-- url     : https://prove2.me/theorems/4fbaccb3-6e7c-453f-b79a-98de2afd859c
-- title:
--   P: standard action mul holds
-- statement:
--   The P construction uses the standard action mul holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Actions.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Actions.lean#L7-L13

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix MvPolynomial

theorem Formalism.UG.P.standard_action_mul_holds : Formalism.UG.StdActMul := by sorry
