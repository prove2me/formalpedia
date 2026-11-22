-- Prove2me | Theorems.Thm_DeciSigma1_disjEntailsTopFreeReg_iff
-- name    : DeciSigma1.disjEntailsTopFreeReg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:25:56.662461+00:00
-- url     : https://prove2.me/theorems/05daa2cc-142a-44d2-aeab-d409996eb950
-- title:
--   Deci Sigma1: disj Entails Top Free Reg iff
-- statement:
--   Over `{⊥, f}`, regular and arbitrary disjunctive entailment agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L327-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L327-L331

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V] {k : ℕ}
omit [DecidableEq V]
omit [Fintype V]

theorem DeciSigma1.disjEntailsTopFreeReg_iff [Finite V] (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg Γ q ↔ DisjEntailsTopFree Γ q := by sorry
