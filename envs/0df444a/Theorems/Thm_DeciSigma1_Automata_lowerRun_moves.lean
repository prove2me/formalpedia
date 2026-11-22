-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_moves
-- name    : DeciSigma1.Automata.lowerRun_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:05.777068+00:00
-- url     : https://prove2.me/theorems/b1fb8839-e82a-4465-934a-f34a1d842a95
-- title:
--   Automata: lower Run moves
-- statement:
--   Every variable of a lower run reaches its target by moves above any suffix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L261-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L261-L269

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

theorem DeciSigma1.Automata.lowerRun_moves {Γ : List (LitT n V)} {y a : V} {γ : List (Fin n)}
    (h : a ∈ lowerRun Γ y γ) (σ : List (Fin n)) : Moves Γ (a, σ) (y, γ ++ σ) := by sorry
