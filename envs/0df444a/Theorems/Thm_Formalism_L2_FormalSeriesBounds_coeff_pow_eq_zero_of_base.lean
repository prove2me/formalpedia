-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_pow_eq_zero_of_base
-- name    : Formalism.L2.FormalSeriesBounds.coeff_pow_eq_zero_of_base
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:28:14.065786+00:00
-- url     : https://prove2.me/theorems/988c0191-bc1a-4765-ac64-4c4a64704b9d
-- title:
--   Formal Series Bounds: coeff pow eq zero of base
-- statement:
--   The Formal Series Bounds construction uses the coeff pow eq zero of base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L698-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L698-L703

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem Formalism.L2.FormalSeriesBounds.coeff_pow_eq_zero_of_base {σ : Type} (Q : σ → Prop) {F : MvPowerSeries σ C}
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) {n : ℕ} (hn : n ≠ 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F ^ n) = 0 := by sorry
