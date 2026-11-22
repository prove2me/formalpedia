-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_reach_iff_cuts_of_not_hasUnaryObstruction
-- name    : DeciSigma1.Full.Closure.reach_iff_cuts_of_not_hasUnaryObstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:20.733467+00:00
-- url     : https://prove2.me/theorems/144a4131-7de4-4336-b2f4-d2dee45d012a
-- title:
--   Closure: reach iff cuts of not has Unary Obstruction
-- statement:
--   The Closure construction uses the reach iff cuts of not has Unary Obstruction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L437-L453
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L437-L453

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

theorem DeciSigma1.Full.Closure.reach_iff_cuts_of_not_hasUnaryObstruction {p q : V × Bool} {u t : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c Γ p u) :
    Reach c Γ (p.1, p.2, u) (q.1, q.2, t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.upperRun (signed c Γ) p (u.take i) ∩
          Automata.lowerRun (signed c Γ) q (t.take e)).Nonempty := by sorry
