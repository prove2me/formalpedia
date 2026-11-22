-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_least_above
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.least_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:58.959175+00:00
-- url     : https://prove2.me/theorems/38bf6726-c56a-4ebd-b333-0377d67a3c2a
-- title:
--   Difference System: least above
-- statement:
--   Given lower bounds `floor` and one solution above them, there is a least solution above
--   them, and every vertex is the end of a duplicate-free path of tight constraints that starts at
--   a vertex where the least solution equals its lower bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L297-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L297-L367

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
open Classical

theorem DeciSigma1.Arithmetic.DifferenceSystem.least_above (floor x0 : ι → ℤ) (h0 : D.Sat x0) (hf : floor ≤ x0) :
    ∃ xm, D.Sat xm ∧ floor ≤ xm ∧ (∀ x, D.Sat x → floor ≤ x → xm ≤ x) ∧
      ∀ i, ∃ p : List ι, p.Nodup ∧ p.getLast? = some i ∧
        (∃ j, p.head? = some j ∧ xm j = floor j) ∧ p.IsChain (D.IsTight xm) := by sorry
