-- Prove2me | Theorems.Thm_FixedOrderFactor_sqrtCount_top_dichotomy
-- name    : FixedOrderFactor.sqrtCount_top_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:08:08.559091+00:00
-- url     : https://prove2.me/theorems/40681286-2281-4131-93cc-f1dcbc85d86d
-- title:
--   Fixed Order Factor: sqrt Count top dichotomy
-- statement:
--   **The class criterion.** `β(M, a, r)` is `0` unless `a` is the square of an element of `H`,
--   and then it equals `β(M, 1, r)`, the number of square roots of `1` in `H`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L214-L217
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L214-L217

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sqrtCount_top_dichotomy {M : ℕ} [NeZero M] {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = if ∃ h : ZMod M, IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1
      then sqrtCount M 1 r else 0 := by sorry
