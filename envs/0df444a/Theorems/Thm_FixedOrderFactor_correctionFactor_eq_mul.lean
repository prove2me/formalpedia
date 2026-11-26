-- Prove2me | Theorems.Thm_FixedOrderFactor_correctionFactor_eq_mul
-- name    : FixedOrderFactor.correctionFactor_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:05:51.919882+00:00
-- url     : https://prove2.me/theorems/89d77138-6b08-5376-b47a-92ecb00427bb
-- title:
--   Fixed Order Factor: correction Factor eq mul
-- statement:
--   Removing finitely many Euler factors multiplies the correction factor by the local ratios.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L72-L75
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L72-L75

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.correctionFactor_eq_mul (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) := by sorry
