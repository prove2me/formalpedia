-- Prove2me | Theorems.Thm_FixedOrderFactor_hasProd_muAvg
-- name    : FixedOrderFactor.hasProd_muAvg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:05:18.111383+00:00
-- url     : https://prove2.me/theorems/0d018e00-db70-59e0-aca5-fb330754c03a
-- title:
--   Fixed Order Factor: has Prod mu Avg
-- statement:
--   **Model mean.** The product of the order-`r` local factors over the primes outside `N`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L44-L47
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L44-L47

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.hasProd_muAvg (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) := by sorry
