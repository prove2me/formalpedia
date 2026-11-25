-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_assemble
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.assemble
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:16.749818+00:00
-- url     : https://prove2.me/theorems/d69ee1a5-2ac5-552c-8981-3116d4473067
-- title:
--   Pl: assemble
-- statement:
--   The Pl construction uses the assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L90-L103

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.assemble {X : Type} {d : ℕ} [NeZero d] (n : ℕ) (hn : n = d) (Emb : Set X) (em : ZMod d → X)
    (hinj : Function.Injective em) (hmem : ∀ a, em a ∈ Emb) (hsurj : ∀ τ ∈ Emb, ∃ a, τ = em a) :
    ∃ (_ : NeZero n) (t : Fin n ≃ Emb) (jj : ZMod d ≃ Fin n),
      (∀ a, jj (a + 1) = jj a + 1) ∧ ∀ a, ((t (jj a) : Emb) : X) = em a := by sorry
