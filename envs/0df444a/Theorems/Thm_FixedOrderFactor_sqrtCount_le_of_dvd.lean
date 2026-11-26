-- Prove2me | Theorems.Thm_FixedOrderFactor_sqrtCount_le_of_dvd
-- name    : FixedOrderFactor.sqrtCount_le_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:34.566378+00:00
-- url     : https://prove2.me/theorems/fdfb29f7-00ed-560b-8970-43022c27766c
-- title:
--   Fixed Order Factor: sqrt Count le of dvd
-- statement:
--   `β` is nondecreasing as `s` decreases along divisibility.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L201-L203
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L201-L203

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sqrtCount_le_of_dvd (M a : ℕ) {s s' : ℕ} (h : s' ∣ s) :
    sqrtCount M a s ≤ sqrtCount M a s' := by sorry
