-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_bounds
-- name    : DeciSigma1.Holes.Fresh.anchors_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:21.582402+00:00
-- url     : https://prove2.me/theorems/1f6a75d2-485b-4285-ae03-d8854f4ceff7
-- title:
--   Fresh: anchors bounds
-- statement:
--   The anchors of a nonempty word are cuts `1 ≤ p ≤ |W l|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L299-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L299-L304

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

theorem DeciSigma1.Holes.Fresh.anchors_bounds {W : Fin k → List α} {t : ℕ} {l : Fin k} (hl : W l ≠ []) {p : ℕ}
    (hp : p ∈ anchors W t l) : 1 ≤ p ∧ p ≤ (W l).length := by sorry
