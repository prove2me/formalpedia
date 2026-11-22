-- Prove2me | Theorems.Thm_DeciSigma1_Automata_derivedPairs_moves
-- name    : DeciSigma1.Automata.derivedPairs_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:22:39.887361+00:00
-- url     : https://prove2.me/theorems/b3612f54-0541-4a72-b01d-580c4623d988
-- title:
--   Automata: derived Pairs moves
-- statement:
--   A derived inequality `a ≤ b` gives a move derivation from `(a, w)` to `(b, w)` for every path
--   `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L239-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L239-L247

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

theorem DeciSigma1.Automata.derivedPairs_moves {Γ : List (LitT n V)} {a b : V} (h : (a, b) ∈ derivedPairs Γ)
    (w : List (Fin n)) : Moves Γ (a, w) (b, w) := by sorry
