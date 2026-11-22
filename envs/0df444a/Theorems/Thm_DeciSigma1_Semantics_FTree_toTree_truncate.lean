-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_truncate
-- name    : DeciSigma1.Semantics.FTree.toTree_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:17.477493+00:00
-- url     : https://prove2.me/theorems/466e14e1-8ad0-4f0f-9696-802b08e2292a
-- title:
--   FTree: to Tree truncate
-- statement:
--   A tree whose domain has depth at most `d` is represented by its truncation at depth `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L308-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L308-L349

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FTree
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}

theorem DeciSigma1.Semantics.FTree.toTree_truncate {d : ℕ} {t : Tree n}
    (hdepth : ∀ π, (t.fn π).isSome → π.length ≤ d) : (truncate d t).toTree = t := by sorry
