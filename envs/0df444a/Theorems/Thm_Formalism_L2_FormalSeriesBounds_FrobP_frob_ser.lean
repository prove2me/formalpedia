-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_frob_ser
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.frob_ser
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:46.761007+00:00
-- url     : https://prove2.me/theorems/18ea0fb1-f569-4333-9d6f-5f32870a0ec9
-- title:
--   Frob P: frob ser
-- statement:
--   The Frob P construction uses the frob ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L122-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L122-L154

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

theorem Formalism.L2.FormalSeriesBounds.FrobP.frob_ser {A B : PowerSeries C} (hA : ∀ n, V.Ge 0 (PowerSeries.coeff n A))
    (hB : ∀ n, V.Ge 0 (PowerSeries.coeff n B)) (m : ℕ) :
    V.MM (PowerSeries.coeff m ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by sorry
