-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_congr
-- name    : Formalism.L2.FormalSeriesBounds.coeff_subst_linS_congr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:46.251688+00:00
-- url     : https://prove2.me/theorems/6369122e-6d06-57f7-a082-12e4988715fc
-- title:
--   Formal Series Bounds: coeff subst lin S congr
-- statement:
--   The Formal Series Bounds construction uses the coeff subst lin S congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L233-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L233-L236

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
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.coeff_subst_linS_congr [Finite σ] (M : τ → σ → C) {F G : MvPowerSeries σ C} {N : ℕ}
    (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G) (e : τ →₀ ℕ) (he : e.degree ≤ N) :
    coeff e (subst (linS M) F) = coeff e (subst (linS M) G) := by sorry
