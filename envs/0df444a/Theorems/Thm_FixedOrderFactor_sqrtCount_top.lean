-- Prove2me | Theorems.Thm_FixedOrderFactor_sqrtCount_top
-- name    : FixedOrderFactor.sqrtCount_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:08:11.460797+00:00
-- url     : https://prove2.me/theorems/a6939a3c-de70-4a8c-ae1d-dd4726983247
-- title:
--   Fixed Order Factor: sqrt Count top
-- statement:
--   **At the top level** (`s = r`): `β(M, a, r)` is the number of square roots of `a` in
--   `H = {h ∈ (ℤ/M)ˣ : h ≡ 1 (mod r)}`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L207-L210
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L207-L210

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sqrtCount_top {M : ℕ} [NeZero M] {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = (Finset.univ.filter fun h : ZMod M =>
      IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1).card := by sorry
