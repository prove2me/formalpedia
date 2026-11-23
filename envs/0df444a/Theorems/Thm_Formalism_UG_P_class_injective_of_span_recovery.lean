-- Prove2me | Theorems.Thm_Formalism_UG_P_class_injective_of_span_recovery
-- name    : Formalism.UG.P.class_injective_of_span_recovery
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:14.116832+00:00
-- url     : https://prove2.me/theorems/183f8161-8644-4e5b-b232-9c71cd2fa97f
-- title:
--   P: class injective of span recovery
-- statement:
--   The P construction uses the class injective of span recovery property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/ClassInjectiveOfSpanRecovery.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/ClassInjectiveOfSpanRecovery.lean#L12-L62

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassInjectiveOfSpanRecovery
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG Formalism.UG.CS

theorem Formalism.UG.P.class_injective_of_span_recovery (hSpanRecover : Formalism.UG.CS.SpanRecover)
    (hGlobLatEquiv : Formalism.UG.CS.GlobLatEquiv) : Formalism.UG.CS.ClassInj := by sorry
