-- Prove2me | Theorems.Thm_FixedOrderFactor_tendsto_modelMean
-- name    : FixedOrderFactor.tendsto_modelMean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:12.832838+00:00
-- url     : https://prove2.me/theorems/e469acad-7c32-4559-90f6-3a41adc42bcc
-- title:
--   Fixed Order Factor: tendsto model Mean
-- statement:
--   The truncated model means converge to `ζ^{(N)}(2) · ζ^{(N)}(r)² / ζ^{(N)}(2r)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L50-L53
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L50-L53

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.tendsto_modelMean (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) := by sorry
