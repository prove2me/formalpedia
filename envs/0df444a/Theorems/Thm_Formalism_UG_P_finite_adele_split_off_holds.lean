-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_adele_split_off_holds
-- name    : Formalism.UG.P.finite_adele_split_off_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:47.063352+00:00
-- url     : https://prove2.me/theorems/f66e546d-0e0e-4d92-8176-1d6daee7b124
-- title:
--   P: finite adele split off holds
-- statement:
--   The P construction uses the finite adele split off holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L485-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L485-L489

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
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

theorem Formalism.UG.P.finite_adele_split_off_holds : Formalism.UG.AfSplitOff := by sorry
