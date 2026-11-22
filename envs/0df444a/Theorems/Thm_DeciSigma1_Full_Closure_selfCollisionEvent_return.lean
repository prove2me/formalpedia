-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_selfCollisionEvent_return
-- name    : DeciSigma1.Full.Closure.selfCollisionEvent_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:56.333025+00:00
-- url     : https://prove2.me/theorems/a4f64c9a-d518-483e-baeb-9b2198bbb8c6
-- title:
--   Closure: self Collision Event return
-- statement:
--   The Closure construction uses the self Collision Event return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L479-L488
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L479-L488

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

theorem DeciSigma1.Full.Closure.selfCollisionEvent_return {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (h : SelfCollisionEvent c Γ p u i j) :
    ∃ δ, Reach c Γ (p.1, p.2, u) (p.1, !p.2, u ++ δ) := by sorry
