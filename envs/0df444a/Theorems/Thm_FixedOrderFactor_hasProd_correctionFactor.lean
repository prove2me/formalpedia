-- Prove2me | Theorems.Thm_FixedOrderFactor_hasProd_correctionFactor
-- name    : FixedOrderFactor.hasProd_correctionFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:02.118032+00:00
-- url     : https://prove2.me/theorems/5699ed5a-8a8e-4e28-86d1-1d88e9604639
-- title:
--   Fixed Order Factor: has Prod correction Factor
-- statement:
--   **Correction factor as an Euler product.**
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L37-L41
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L37-L41

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.hasProd_correctionFactor (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) := by sorry
