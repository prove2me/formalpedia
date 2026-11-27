-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_resid
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.resid
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:16.318295+00:00
-- url     : https://prove2.me/theorems/ce5f4cf2-813f-4303-807b-af1c1fda2a01
-- title:
--   Gm Ex Arith: resid
-- statement:
--   The Gm Ex Arith construction uses the resid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L279-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L279-L391

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.resid {R : Type} [CommRing R] {d : ℕ} [NeZero d] (ψ : ZMod d → R →+* C)
    (hint : ∀ a x, V.Ge 0 (ψ a x)) (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l))
    (sep : ∀ a : ZMod d, a ≠ 0 → ∃ x, ¬ V.MM (ψ a x - ψ 0 x)) (hl2 : V.l ≠ 2) :
    ∃ x : R, V.MM (ψ 0 x ^ ((V.l ^ d - 1) / 2) + 1) := by sorry
