-- Prove2me | Theorems.Thm_DeciSigma1_Examples_pinned_sat
-- name    : DeciSigma1.Examples.pinned_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:29.493813+00:00
-- url     : https://prove2.me/theorems/34be6708-209e-49b1-b60e-199fa899d85a
-- title:
--   Examples: pinned sat
-- statement:
--   The Examples construction uses the pinned sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L114-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L114-L118

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints

theorem DeciSigma1.Examples.pinned_sat {c : Fin 2 → Bool} {s : Fin 2 → Fin 4} {ρ : Fin 4 → Semantics.Tree 2}
    (h : SatT c ρ (pinned s)) :
    ρ 1 = Tree.bot ∧ ρ 2 = Tree.top ∧ ρ 3 = Semantics.Tree.node (ρ ∘ s) := by sorry
