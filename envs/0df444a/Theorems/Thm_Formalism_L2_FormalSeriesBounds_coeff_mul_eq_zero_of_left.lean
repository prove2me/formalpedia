-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_eq_zero_of_left
-- name    : Formalism.L2.FormalSeriesBounds.coeff_mul_eq_zero_of_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:25:30.892902+00:00
-- url     : https://prove2.me/theorems/39276042-3569-5975-aba7-97e44852c7ea
-- title:
--   Formal Series Bounds: coeff mul eq zero of left
-- statement:
--   The Formal Series Bounds construction uses the coeff mul eq zero of left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L680-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L680-L689

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

theorem Formalism.L2.FormalSeriesBounds.coeff_mul_eq_zero_of_left {σ : Type} (Q : σ → Prop) {F : MvPowerSeries σ C}
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) (G : MvPowerSeries σ C)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F * G) = 0 := by sorry
