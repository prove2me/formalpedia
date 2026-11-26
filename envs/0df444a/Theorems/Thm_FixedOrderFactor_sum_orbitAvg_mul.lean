-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_orbitAvg_mul
-- name    : FixedOrderFactor.sum_orbitAvg_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:10.29362+00:00
-- url     : https://prove2.me/theorems/3a3f3680-3741-5ad9-9c24-093c01b14b5d
-- title:
--   Fixed Order Factor: sum orbit Avg mul
-- statement:
--   **The orbit average on a Frobenius class.** `∑_{t<s} ϱ_s(ct)` is `s` if `s ∣ c` and `0`
--   otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L167-L169
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L167-L169

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sum_orbitAvg_mul {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ Finset.range s, orbitAvg s (c * t) = if s ∣ c then (s : ℂ) else 0 := by sorry
