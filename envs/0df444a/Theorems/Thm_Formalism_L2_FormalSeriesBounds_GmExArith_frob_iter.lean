-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_frob_iter
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.frob_iter
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:32.287889+00:00
-- url     : https://prove2.me/theorems/e1fc84f2-b511-5d72-bac1-c9232dfaaf9d
-- title:
--   Gm Ex Arith: frob iter
-- statement:
--   The Gm Ex Arith construction uses the frob iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L266-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L266-L277

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.GmExArith.frob_iter {R : Type} [CommRing R] {d : ℕ} (ψ : ZMod d → R →+* C) (hint : ∀ a x, V.Ge 0 (ψ a x))
    (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l)) (x : R) (j : ℕ) :
    V.MM (ψ (j : ZMod d) x - ψ 0 x ^ (V.l ^ j)) := by sorry
