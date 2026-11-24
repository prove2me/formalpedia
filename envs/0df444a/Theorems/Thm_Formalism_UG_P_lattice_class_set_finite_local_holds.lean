-- Prove2me | Theorems.Thm_Formalism_UG_P_lattice_class_set_finite_local_holds
-- name    : Formalism.UG.P.lattice_class_set_finite_local_holds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:51.384194+00:00
-- url     : https://prove2.me/theorems/a4707484-064c-42b8-9b07-7641dbbc5d62
-- title:
--   P: lattice class set finite local holds
-- statement:
--   The P construction uses the lattice class set finite local holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/ClassSet.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/ClassSet.lean#L16-L20

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsTrace
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassInjectiveOfSpanRecovery
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEquiv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassSetFiniteBoundedHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.lattice_class_set_finite_local_holds : Formalism.UG.ClassSetFiniteL := by sorry
