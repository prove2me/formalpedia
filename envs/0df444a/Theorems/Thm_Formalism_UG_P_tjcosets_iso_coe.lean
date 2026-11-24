-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_iso_coe
-- name    : Formalism.UG.P.tjcosets_iso_coe
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:27.157446+00:00
-- url     : https://prove2.me/theorems/6fba4dc1-0aaa-4b98-82bb-15c12dede300
-- title:
--   P: tjcosets iso coe
-- statement:
--   The P construction uses the tjcosets iso coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L55-L57

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

theorem Formalism.UG.P.tjcosets_iso_coe (n : ℕ) (O : Subring L) (g : GL (Fin n) O) :
    ((tjcosets_iso n O g : GLint (Fin n) O) : GL (Fin n) L) = bc O.subtype g := by sorry
