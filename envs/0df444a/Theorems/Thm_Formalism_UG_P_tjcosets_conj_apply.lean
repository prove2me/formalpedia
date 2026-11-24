-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_conj_apply
-- name    : Formalism.UG.P.tjcosets_conj_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:43.370783+00:00
-- url     : https://prove2.me/theorems/5080918c-c00c-4968-b5b4-731bdc091077
-- title:
--   P: tjcosets conj apply
-- statement:
--   The P construction uses the tjcosets conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L108-L117

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
variable (O : Subring L) [IsLocalRing O]
variable {O}

theorem Formalism.UG.P.tjcosets_conj_apply (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) (g : GL (Fin n) L) (a b : Fin n) :
    (((tjcosets_dG n j ϖ hϖ)⁻¹ * g * tjcosets_dG n j ϖ hϖ : GL (Fin n) L) :
        Matrix (Fin n) (Fin n) L) a b =
      (if (a : ℕ) < j then ϖ⁻¹ else 1) * (g : Matrix (Fin n) (Fin n) L) a b *
        (if (b : ℕ) < j then ϖ else 1) := by sorry
