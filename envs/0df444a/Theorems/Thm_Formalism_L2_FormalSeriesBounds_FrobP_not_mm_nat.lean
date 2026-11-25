-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_not_mm_nat
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.not_mm_nat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:39.803804+00:00
-- url     : https://prove2.me/theorems/9f68b48f-4ddc-418f-a87e-b52021eb9b07
-- title:
--   Frob P: not mm nat
-- statement:
--   The Frob P construction uses the not mm nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L30-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L30-L50

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

theorem Formalism.L2.FormalSeriesBounds.FrobP.not_mm_nat {m : ℕ} (hm : ¬ V.l ∣ m) : ¬ V.MM (m : C) := by sorry
