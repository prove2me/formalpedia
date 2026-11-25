-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_subst_linS
-- name    : Formalism.L2.FormalSeriesBounds.dVar_subst_linS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:38.185341+00:00
-- url     : https://prove2.me/theorems/a2d43004-9c2f-4e06-9219-d39d2b699154
-- title:
--   Formal Series Bounds: d Var subst lin S
-- statement:
--   The Formal Series Bounds construction uses the d Var subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L266-L270

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

theorem Formalism.L2.FormalSeriesBounds.dVar_subst_linS {C : Type} [Field C] {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C)
    (b : τ) (H : MvPowerSeries σ C) :
    dVar b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (dVar w H) := by sorry
