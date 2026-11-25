-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_prod_eq_zero_of_mem
-- name    : Formalism.L2.FormalSeriesBounds.coeff_prod_eq_zero_of_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:03:32.525321+00:00
-- url     : https://prove2.me/theorems/3238632c-8284-4e66-bc0f-ed376b3fffbc
-- title:
--   Formal Series Bounds: coeff prod eq zero of mem
-- statement:
--   The Formal Series Bounds construction uses the coeff prod eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L691-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L691-L696

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

theorem Formalism.L2.FormalSeriesBounds.coeff_prod_eq_zero_of_mem {σ ρ : Type} (Q : σ → Prop) (s : Finset ρ)
    (F : ρ → MvPowerSeries σ C) {w : ρ} (hw : w ∈ s)
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M (F w) = 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (∏ i ∈ s, F i) = 0 := by sorry
