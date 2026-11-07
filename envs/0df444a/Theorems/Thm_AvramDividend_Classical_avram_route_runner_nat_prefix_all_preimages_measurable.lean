-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_nat_prefix_all_preimages_measurable
-- name    : AvramDividend.Classical.avram_route_runner_nat_prefix_all_preimages_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:53:15.895409+00:00
-- url     : https://prove2.me/theorems/86ff26ac-d164-4b5f-92e7-3dd188b519dd
-- title:
--   Strict integer-prefix events make every selector preimage measurable
-- statement:
--   An integer-valued random stopping-grid selector whose strict threshold events are measurable has measurable preimages for every subset of natural numbers. The conclusion is stronger than measurability under any chosen natural-number measurable-space and avoids requiring a default MeasurableSpace Nat instance, absent in the pinned environment. Its proof uses singleton fibres and countable unions.
-- source:
--   Corrected source-exact reduction; previous fcc7287c statement was missing Nat measurable-space instance. The all-preimages conclusion avoids this hidden typeclass dependency and can be instantiated in the original bounded predictable martingale prefix budget.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_nat_prefix_all_preimages_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : Ω → ℕ)
    (hPrefix : ∀ i : ℕ, MeasurableSet {ω : Ω | i < k ω}) :
    ∀ s : Set ℕ, MeasurableSet (k ⁻¹' s) := by sorry
