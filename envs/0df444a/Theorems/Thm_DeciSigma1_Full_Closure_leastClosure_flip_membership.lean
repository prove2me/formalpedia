-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_flip_membership
-- name    : DeciSigma1.Full.Closure.leastClosure_flip_membership
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:20.854941+00:00
-- url     : https://prove2.me/theorems/86a3b145-68b5-47e0-9e59-1eded441dad0
-- title:
--   Closure: least Closure flip membership
-- statement:
--   The opposite sign of `(p, t)` lies in the least closure exactly when the upper run of `p` on
--   some prefix of `t`, with exchanged signs, meets the signed variables reachable from facts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L377-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L377-L386

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
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}

theorem DeciSigma1.Full.Closure.leastClosure_flip_membership {p : V × Bool} {t : List (Fin n)} :
    (p.1, !p.2, t) ∈ leastClosure c Γ ↔
      ∃ e ≤
          t.length, FlippedIntersectsFacts c Γ
              (Automata.upperRun (signed c Γ) p (t.take e)) := by sorry
