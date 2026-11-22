-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_membership
-- name    : DeciSigma1.Full.Closure.leastClosure_membership
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:23.874848+00:00
-- url     : https://prove2.me/theorems/53214bad-7e9c-43bd-b532-9b644326aaf1
-- title:
--   Closure: least Closure membership
-- statement:
--   A signed configuration lies in the least closure exactly when the lower run of its signed
--   variable on some prefix of its path meets the signed variables reachable from facts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L310-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L310-L331

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

theorem DeciSigma1.Full.Closure.leastClosure_membership {q : V} {s : Bool} {t : List (Fin n)} :
    (q, s, t) ∈ leastClosure c Γ ↔ ∃ e ≤ t.length,
      (Automata.lowerRun (signed c Γ) (q,
          s) (t.take e) ∩ factReachableVariables c Γ).Nonempty := by sorry
