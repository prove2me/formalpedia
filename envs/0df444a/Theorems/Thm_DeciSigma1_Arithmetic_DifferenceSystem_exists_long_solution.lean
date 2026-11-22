-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_long_solution
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.exists_long_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:59.248917+00:00
-- url     : https://prove2.me/theorems/8ea8b5f6-c5d8-4a2a-a9af-3c107403f176
-- title:
--   Difference System: exists long solution
-- statement:
--   A system without positive cycles has a natural-number solution above any lower bounds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L269-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L269-L285

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.exists_long_solution [Finite ι] (D : DifferenceSystem ι)
    (h : ¬ D.HasPositiveCycle) (lower : ι → ℕ) :
    ∃ L : ι → ℕ, D.Sat (fun i => (L i : ℤ)) ∧ ∀ i, lower i ≤ L i := by sorry
