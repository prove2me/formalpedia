-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_eq_zero
-- name    : Formalism.L2.FormalSeriesBounds.coeff_subst_linS_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:00.277885+00:00
-- url     : https://prove2.me/theorems/8dd5b15f-faa6-5067-a871-e0d7a85f2a39
-- title:
--   Formal Series Bounds: coeff subst lin S eq zero
-- statement:
--   The Formal Series Bounds construction uses the coeff subst lin S eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L705-L731
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L705-L731

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

theorem Formalism.L2.FormalSeriesBounds.coeff_subst_linS_eq_zero {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C) (R : σ → Prop)
    (Q : τ → Prop) (hRQ : ∀ w, R w → ∀ c, ¬ Q c → M c w = 0) (H : MvPowerSeries σ C)
    (hH : ∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, ¬ R w) → coeff μ H = 0)
    (A : τ →₀ ℕ) (hA : ∀ b, Q b → A b = 0) : coeff A (subst (linS M) H) = 0 := by sorry
