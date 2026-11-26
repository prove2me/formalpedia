-- Prove2me | Theorems.Thm_FixedNumerator_sign_class_invariant
-- name    : FixedNumerator.sign_class_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:37.939527+00:00
-- url     : https://prove2.me/theorems/833f9e59-e868-497f-931d-6dd690188278
-- title:
--   Fixed Numerator: sign class invariant
-- statement:
--   The sign `(-1)^{C(a, c)}` depends only on the class of `a` modulo `4` (for `a` in a primary
--   class).
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L51-L53
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L51-L53

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator

theorem FixedNumerator.sign_class_invariant (a b c : GaussianInt) (hb : IsPrimary b)
    (h : (4 : GaussianInt) ∣ a - b) : (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c := by sorry
