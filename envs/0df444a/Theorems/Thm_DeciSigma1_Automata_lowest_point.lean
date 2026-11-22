-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowest_point
-- name    : DeciSigma1.Automata.lowest_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:29.612208+00:00
-- url     : https://prove2.me/theorems/012d08fc-b9b1-4e68-b57b-3810de28f3b3
-- title:
--   Automata: lowest point
-- statement:
--   A move derivation from `(x, u)` to `(y, t)` exists exactly when, for a common suffix
--   `u.drop s = t.drop e`, the upper run of `x` on `u.take s` meets the lower run of `y` on
--   `t.take e`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L362-L376
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L362-L376

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

theorem DeciSigma1.Automata.lowest_point {Γ : List (LitT n V)} {x y : V} {u t : List (Fin n)} :
    Moves Γ (x, u) (y, t) ↔ ∃ s ≤ u.length, ∃ e ≤ t.length,
      u.drop s = t.drop e ∧
      (upperRun Γ x (u.take s) ∩ lowerRun Γ y (t.take e)).Nonempty := by sorry
