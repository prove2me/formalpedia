-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_upperRun_iff_moves
-- name    : DeciSigma1.Automata.mem_upperRun_iff_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:59.031638+00:00
-- url     : https://prove2.me/theorems/0aeb1e92-1956-4576-80e1-dd9a1052eb49
-- title:
--   Automata: mem upper Run iff moves
-- statement:
--   The upper run on `β` is the set of variables whose root is reached from `(x, β)` by moves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L348-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L348-L357

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.mem_upperRun_iff_moves {Γ : List (LitT n V)} {x b : V} (β : List (Fin n)) :
    b ∈ upperRun Γ x β ↔ Moves Γ (x, β) (b, []) := by sorry
