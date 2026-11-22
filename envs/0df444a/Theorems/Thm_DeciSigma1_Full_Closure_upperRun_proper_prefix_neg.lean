-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_upperRun_proper_prefix_neg
-- name    : DeciSigma1.Full.Closure.upperRun_proper_prefix_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:16.982545+00:00
-- url     : https://prove2.me/theorems/87951246-889e-4249-b048-621d4b261061
-- title:
--   Closure: upper Run proper prefix neg
-- statement:
--   If the upper run on `γ` is nonempty, the upper run on every proper prefix of `γ` meets the
--   signed variables below a negative fact.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L399-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L399-L407

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

theorem DeciSigma1.Full.Closure.upperRun_proper_prefix_neg {p : V × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.upperRun (signed c Γ) p γ).Nonempty) (hi : i < γ.length) :
    (Automata.upperRun (signed c Γ) p
        (γ.take i) ∩ forbiddenPredecessors c Γ).Nonempty := by sorry
