-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_sign_coherent
-- name    : DeciSigma1.Full.Closure.sign_coherent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:00.543775+00:00
-- url     : https://prove2.me/theorems/19ab8b12-6561-449b-87d7-56b02cd21f91
-- title:
--   Closure: sign coherent
-- statement:
--   All signed variables in an upper run state have the sign of the start shifted by the polarity of
--   the path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L206-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L206-L212

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Closure.sign_coherent {p : V} {s : Bool} {r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Automata.upperRun (signed c Γ) (p, s) w) :
    r.2 = Bool.xor s (polarity c w) := by sorry
