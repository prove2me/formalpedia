-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_le_local
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_le_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:49.477188+00:00
-- url     : https://prove2.me/theorems/3604ee06-5d7c-4174-9865-de54c957a07d
-- title:
--   Difference System: weight le local
-- statement:
--   Along a walk inside a set on which `x` satisfies every constraint, `x` grows at least by the
--   weight of the walk.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L146-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L146-L161

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_le_local {ι : Type}
    {D : DifferenceSystem ι} {x : ι → ℤ} (P : ι → Prop)
    (hP : ∀ u v c, P u → P v → D.edgeWeight u v = some c → x u + c ≤ x v) :
    ∀ (i : ι) (q : List ι), D.IsWalk (i :: q) → (∀ z ∈ i :: q, P z) →
      x i + D.weight (i :: q) ≤ x ((i :: q).getLast (List.cons_ne_nil _ _))
  := by sorry
