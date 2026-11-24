-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_mem_max
-- name    : Formalism.UG.P.tjcosets_mem_max
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:38:18.337801+00:00
-- url     : https://prove2.me/theorems/e28e68e0-ddc4-4a2a-bac4-998d43d5b843
-- title:
--   P: tjcosets mem max
-- statement:
--   The P construction uses the tjcosets mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L86-L93

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.tjcosets_mem_max (x : Ov F v) :
    IsLocalRing.residue (Ov F v) x = 0 ↔ Valued.v (x : v.adicCompletion F) < 1 := by sorry
