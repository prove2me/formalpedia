-- Prove2me | Theorems.Thm_Formalism_UG_P_adelic_stabilizer_finite_lattice_holds
-- name    : Formalism.UG.P.adelic_stabilizer_finite_lattice_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:14.724165+00:00
-- url     : https://prove2.me/theorems/fe577cba-62bd-48b4-9f3a-2afb8b072bcd
-- title:
--   P: adelic stabilizer finite lattice holds
-- statement:
--   The P construction uses the adelic stabilizer finite lattice holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L125-L129

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
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
open Formalism.UG

theorem Formalism.UG.P.adelic_stabilizer_finite_lattice_holds : Formalism.UG.AdelicStabFiniteL := by sorry
