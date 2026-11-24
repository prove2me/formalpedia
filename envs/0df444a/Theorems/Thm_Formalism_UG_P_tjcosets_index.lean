-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_index
-- name    : Formalism.UG.P.tjcosets_index
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:16.168299+00:00
-- url     : https://prove2.me/theorems/2e9bf3e7-17b2-408d-bd60-26af0112695b
-- title:
--   P: tjcosets index
-- statement:
--   The P construction uses the tjcosets index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L215-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L215-L222

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

theorem Formalism.UG.P.tjcosets_index (n j : ℕ) (ϖ : L) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] :
    Nat.card {x : GL (Fin n) L ⧸ GLint (Fin n) O // ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
        x.out = a * tjcosets_dG n j ϖ hϖ * b} =
      (tjcosets_par (𝔽 := IsLocalRing.ResidueField O) n j).index := by sorry
