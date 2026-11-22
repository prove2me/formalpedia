-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_lowest_point_leaf
-- name    : DeciSigma1.Full.Closure.lowest_point_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:10.766456+00:00
-- url     : https://prove2.me/theorems/5c0c5d4d-1d20-482d-b7ad-d8bead440226
-- title:
--   Closure: lowest point leaf
-- statement:
--   The Closure construction uses the lowest point leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L196-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L196-L202

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

theorem DeciSigma1.Full.Closure.lowest_point_leaf {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c Γ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.upperRun (signed c Γ) (p, s) (u.take i) ∩
          Automata.lowerRun (signed c Γ) (q, s') (t.take e)).Nonempty := by sorry
