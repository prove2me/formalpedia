-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_valuation_coeff_mul_nonneg
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_mul_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:36:00.525021+00:00
-- url     : https://prove2.me/theorems/edfee490-c91c-4f8c-a3e7-615db87d704c
-- title:
--   Frob P: valuation coeff mul nonneg
-- statement:
--   The Frob P construction uses the valuation coeff mul nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L94-L105

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

theorem Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_mul_nonneg {f g : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f))
    (hg : ∀ n, V.Ge 0 (PowerSeries.coeff n g)) : ∀ n, V.Ge 0 (PowerSeries.coeff n (f * g)) := by sorry
