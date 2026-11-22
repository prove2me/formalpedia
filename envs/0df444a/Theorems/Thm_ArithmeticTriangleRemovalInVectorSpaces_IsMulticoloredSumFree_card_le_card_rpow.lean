-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_le_card_rpow
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_card_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:12.420233+00:00
-- url     : https://prove2.me/theorems/92929bf6-9d38-402f-9e5e-94796d11ff64
-- title:
--   Is Multicolored Sum Free: card le card rpow
-- statement:
--   **The Kleinberg–Sawin–Speyer bound.** A multicolored sum-free family in a finite vector space
--   `G` over `ZMod p` has at most `#G ^ (1 - c p)` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/TensorPower.lean#L80-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/TensorPower.lean#L80-L93

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
set_option autoImplicit true
@[expose] public section
public section
open Finset Module
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {G ι : Type*} [AddCommGroup G] [Module (ZMod p) G] [Fintype ι]
  {x y z : ι → G}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_card_rpow [Fintype G] (h : IsMulticoloredSumFree x y z) :
    (Fintype.card ι : ℝ) ≤ Fintype.card G ^ (1 - c p) := by sorry
