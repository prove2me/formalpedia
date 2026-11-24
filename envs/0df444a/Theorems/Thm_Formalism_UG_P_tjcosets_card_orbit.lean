-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_card_orbit
-- name    : Formalism.UG.P.tjcosets_card_orbit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:27.399786+00:00
-- url     : https://prove2.me/theorems/03e7c4e0-70ff-43a0-8484-2088fe4c49c4
-- title:
--   P: tjcosets card orbit
-- statement:
--   The P construction uses the tjcosets card orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L16-L38

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]

theorem Formalism.UG.P.tjcosets_card_orbit {G : Type} [Group G] (K : Subgroup G) (d : G) :
    Nat.card {x : G ⧸ K // ∃ a ∈ K, ∃ b ∈ K, x.out = a * d * b} =
      (MulAction.stabilizer K (QuotientGroup.mk d : G ⧸ K)).index := by sorry
