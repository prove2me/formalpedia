-- Prove2me | Theorems.Thm_BalanceSpecification_marker_suffixLength_strictMono
-- name    : BalanceSpecification.marker_suffixLength_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:15.638717+00:00
-- url     : https://prove2.me/theorems/84563cb3-4e81-4d95-8562-eb911d1ec47d
-- title:
--   Balance Specification: marker suffix Length strict Mono
-- statement:
--   The source's common-tail lengths increase strictly under sparse growth.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L123-L132
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L123-L132

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.marker_suffixLength_strictMono {s : ℕ → ℕ} {M : ℕ}
    (hpos : ∀ n, 0 < s n) (hgap : ∀ n, 2 * s n < s (n + 1))
    (hlow : ∀ n, n + M ≤ s n) : StrictMono (fun n => s n - n - M) := by sorry
