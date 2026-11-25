-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_mm_of_mul_nat
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.mm_of_mul_nat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:58.707015+00:00
-- url     : https://prove2.me/theorems/454a22ca-0bab-4990-8561-7b7690a320d6
-- title:
--   Frob P: mm of mul nat
-- statement:
--   The Frob P construction uses the mm of mul nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L52-L58

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.FrobP.mm_of_mul_nat {c : C} {m : ℕ} (hm : ¬ V.l ∣ m) (h : V.MM (c * m)) : V.MM c := by sorry
