-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_quot_conjInter
-- name    : Formalism.UG.P.finite_quot_conjInter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:49.513859+00:00
-- url     : https://prove2.me/theorems/75b2a2ac-ab6a-45ff-b9d2-108432259ae0
-- title:
--   P: finite quot conj Inter
-- statement:
--   The P construction uses the finite quot conj Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean#L14-L17

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.finite_quot_conjInter {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by sorry
