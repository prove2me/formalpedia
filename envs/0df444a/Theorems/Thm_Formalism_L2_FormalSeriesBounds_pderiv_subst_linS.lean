-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst_linS
-- name    : Formalism.L2.FormalSeriesBounds.pderiv_subst_linS
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:02.45927+00:00
-- url     : https://prove2.me/theorems/76a6e377-5cfb-4910-8755-7213f28305be
-- title:
--   Formal Series Bounds: pderiv subst lin S
-- statement:
--   The Formal Series Bounds construction uses the pderiv subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L247-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L247-L251

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

theorem Formalism.L2.FormalSeriesBounds.pderiv_subst_linS [Fintype σ] (M : τ → σ → C) (b : τ) (H : MvPowerSeries σ C) :
    pderiv C b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (pderiv C w H) := by sorry
