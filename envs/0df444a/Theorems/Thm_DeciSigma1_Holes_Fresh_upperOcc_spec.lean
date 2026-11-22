-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
-- name    : DeciSigma1.Holes.Fresh.upperOcc_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:28.894824+00:00
-- url     : https://prove2.me/theorems/177ea43f-9763-4af8-b713-acf8c033310e
-- title:
--   Fresh: upper Occ spec
-- statement:
--   Basic facts on an upper occurrence `(l, s, e)`: `s < e ≤ |W l|`, `e` is a lower anchor,
--   `s` is `0` or a lower anchor, and no upper anchor lies strictly between `s` and `e`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L353-L377
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L353-L377

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.upperOcc_spec {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    o.2.1 < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧ o.2.2 ∈ anchors W t o.1 ∧
      (o.2.1 = 0 ∨ o.2.1 ∈ anchors W t o.1) ∧
      ∀ p ∈ anchors W (t + 1) o.1, ¬ (o.2.1 < p ∧ p < o.2.2) := by sorry
