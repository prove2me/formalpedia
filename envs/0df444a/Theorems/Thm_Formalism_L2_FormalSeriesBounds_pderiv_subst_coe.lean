-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst_coe
-- name    : Formalism.L2.FormalSeriesBounds.pderiv_subst_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:09.324828+00:00
-- url     : https://prove2.me/theorems/0a99f6ed-fd7e-4b3e-9b7f-9604033b1884
-- title:
--   Formal Series Bounds: pderiv subst coe
-- statement:
--   The Formal Series Bounds construction uses the pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L103-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L103-L146

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
variable {C : Type*} [Field C] {σ τ : Type*}

theorem Formalism.L2.FormalSeriesBounds.pderiv_subst_coe [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (b : τ)
    (p : MvPolynomial σ C) :
    pderiv C b (subst a (p : MvPowerSeries σ C)) =
      ∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C)) := by sorry
