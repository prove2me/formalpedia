-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rename_subst_linS
-- name    : Formalism.L2.FormalSeriesBounds.rename_subst_linS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:25:11.700124+00:00
-- url     : https://prove2.me/theorems/69d637bd-3940-5354-ac54-b1cafa2e8493
-- title:
--   Formal Series Bounds: rename subst lin S
-- statement:
--   The Formal Series Bounds construction uses the rename subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L329-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L329-L335

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

theorem Formalism.L2.FormalSeriesBounds.rename_subst_linS {σ τ τ' : Type} [Fintype σ] [Fintype τ] (f : τ ↪ τ') (M : τ → σ → C)
    (F : MvPowerSeries σ C) :
    rename f (subst (linS M) F) = subst (fun x => rename f (linS M x)) F := by sorry
