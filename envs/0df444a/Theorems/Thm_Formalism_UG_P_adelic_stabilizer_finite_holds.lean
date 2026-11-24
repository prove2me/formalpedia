-- Prove2me | Theorems.Thm_Formalism_UG_P_adelic_stabilizer_finite_holds
-- name    : Formalism.UG.P.adelic_stabilizer_finite_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:06.139195+00:00
-- url     : https://prove2.me/theorems/154725ab-e661-4d49-9a92-38f17bc8cf54
-- title:
--   P: adelic stabilizer finite holds
-- statement:
--   The P construction uses the adelic stabilizer finite holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L310-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L310-L321

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
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

theorem Formalism.UG.P.adelic_stabilizer_finite_holds : Formalism.UG.AdelicStabFinite := by sorry
