-- Prove2me | Theorems.Thm_DeciSigma1_Automata_upperRun_moves
-- name    : DeciSigma1.Automata.upperRun_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:52.694613+00:00
-- url     : https://prove2.me/theorems/630c2e77-c0b2-4825-9f3d-ff162605c913
-- title:
--   Automata: upper Run moves
-- statement:
--   Every variable of an upper run is reached by moves above any suffix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L250-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L250-L258

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

theorem DeciSigma1.Automata.upperRun_moves {Γ : List (LitT n V)} {x b : V} {β : List (Fin n)}
    (h : b ∈ upperRun Γ x β) (σ : List (Fin n)) : Moves Γ (x, β ++ σ) (b, σ) := by sorry
