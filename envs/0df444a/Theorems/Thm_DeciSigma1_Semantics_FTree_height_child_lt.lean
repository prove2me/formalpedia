-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_height_child_lt
-- name    : DeciSigma1.Semantics.FTree.height_child_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:51.293039+00:00
-- url     : https://prove2.me/theorems/5b1fc0b0-f62f-4aff-9b7e-a25b5b5426d9
-- title:
--   FTree: height child lt
-- statement:
--   The FTree construction uses the height child lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L169-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L169-L173

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
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}

theorem DeciSigma1.Semantics.FTree.height_child_lt (a : Fin n → FTree n) (i : Fin n) :
    (a i).height < (node a).height := by sorry
