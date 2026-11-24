-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_hmax
-- name    : Formalism.UG.P.tjcosets_hmax
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:03.50155+00:00
-- url     : https://prove2.me/theorems/ba481115-574f-4905-a0a7-8606237de63e
-- title:
--   P: tjcosets hmax
-- statement:
--   The P construction uses the tjcosets hmax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L101-L112

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

theorem Formalism.UG.P.tjcosets_hmax (ϖ : v.adicCompletion F) (hϖ : IsUnifV F v ϖ) (x : Ov F v) :
    ϖ⁻¹ * (x : v.adicCompletion F) ∈ Ov F v ↔ IsLocalRing.residue (Ov F v) x = 0 := by sorry
