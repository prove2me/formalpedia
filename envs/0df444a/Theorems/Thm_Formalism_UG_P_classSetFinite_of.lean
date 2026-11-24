-- Prove2me | Theorems.Thm_Formalism_UG_P_classSetFinite_of
-- name    : Formalism.UG.P.classSetFinite_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:58.17895+00:00
-- url     : https://prove2.me/theorems/d18eef12-2f24-4eaf-b35f-a4cfeda47a26
-- title:
--   P: class Set Finite of
-- statement:
--   The P construction uses the class Set Finite of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsAsmHformSmulRight.lean#L130-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsAsmHformSmulRight.lean#L130-L176

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
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

theorem Formalism.UG.P.classSetFinite_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFinite := by sorry
