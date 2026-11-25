-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_coeff_pow_char_frobenius
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.coeff_pow_char_frobenius
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:49.530888+00:00
-- url     : https://prove2.me/theorems/c572e8c2-48b5-46d4-935d-b8862b4e77f6
-- title:
--   Frob P: coeff pow char frobenius
-- statement:
--   The Frob P construction uses the coeff pow char frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L156-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L156-L238

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

theorem Formalism.L2.FormalSeriesBounds.FrobP.coeff_pow_char_frobenius : ∀ (m : ℕ) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
    V.MM (PowerSeries.coeff m (f ^ V.l) - if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) := by sorry
