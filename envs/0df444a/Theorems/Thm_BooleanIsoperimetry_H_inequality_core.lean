-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_inequality_core
-- name    : BooleanIsoperimetry.H_inequality_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:52.7244+00:00
-- url     : https://prove2.me/theorems/7ed80c18-a33d-46b5-bd41-8a9f1a9c60a3
-- title:
--   Boolean Isoperimetry: H inequality core
-- statement:
--   The Harper boundary inequality, stated directly on `H`:
--   `H (n+1) (a+b) ≤ max (H n a) b + max (H n b) a`.
--
--   Via `H_succ_cascade` this is equivalent to `macaulay_optimization` (the canonical
--   cascade split of `a+b` minimises the cross boundary expression), so it is the
--   genuine combinatorial heart of Harper's vertex-isoperimetric theorem for the
--   discrete cube.
--
--   The supporting structure for this statement is fully developed above:
--   * `H_succ_cascade`         — the slice recursion `H (n+1) k = max (H n p) q + max (H n q) p`;
--   * `cascade_p_le_H_q`       — the compression property `p ≤ H n q` of the canonical split;
--   * `cascade_q_le_p`         — `q ≤ p`;
--   * `H_mono`, `H_ge_self`, `H_le_cube`, `H_add_self_mono` — monotonicity / growth of `H`;
--   * `H_eq_gShift_count`      — the explicit boundary count formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2073-L2087
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2073-L2087

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.H_inequality_core :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by sorry
