-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_entries
-- name    : Formalism.UG.P.tjcosets_entries
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:54.179906+00:00
-- url     : https://prove2.me/theorems/1ae958e0-5da3-424f-a7c1-7543ec8c4054
-- title:
--   P: tjcosets entries
-- statement:
--   The P construction uses the tjcosets entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L148-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L148-L173

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

theorem Formalism.UG.P.tjcosets_entries (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] (h : GL (Fin n) O) (hϖO : ϖ ∈ O) :
    (∀ a b : Fin n, (if (a : ℕ) < j then ϖ⁻¹ else 1) *
        (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * (if (b : ℕ) < j then ϖ else 1) ∈ O) ↔
      bc (IsLocalRing.residue O) h ∈ tjcosets_par n j := by sorry
