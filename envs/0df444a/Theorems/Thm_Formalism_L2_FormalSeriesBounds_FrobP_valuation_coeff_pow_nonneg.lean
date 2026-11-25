-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_valuation_coeff_pow_nonneg
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_pow_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:56.247697+00:00
-- url     : https://prove2.me/theorems/9ffdd22a-a7dc-4cd5-a099-8769207e1fb5
-- title:
--   Frob P: valuation coeff pow nonneg
-- statement:
--   The Frob P construction uses the valuation coeff pow nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L107-L120

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

theorem Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_pow_nonneg {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) (k : ℕ) :
    ∀ n, V.Ge 0 (PowerSeries.coeff n (f ^ k)) := by sorry
