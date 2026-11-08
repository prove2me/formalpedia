-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_nat_prefix_masks_measurable
-- name    : AvramDividend.Classical.avram_route_runner_nat_prefix_masks_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:45:55.34174+00:00
-- url     : https://prove2.me/theorems/fcc7287c-2aa5-411a-9eb7-3b7f70ead3c2
-- title:
--   A Nat-valued stopping-prefix selector is measurable from all strict prefix events
-- statement:
--   Measurability of every strict threshold event {i < k(ω)} determines measurability of the integer-valued random prefix k. Each singleton inverse image {k=n} is a difference of adjacent threshold events (the zero case is a complement); every inverse image of an arbitrary Nat subset is the countable union of its singleton fibres. This closes the measurability side condition in the original predictable martingale bounded-prefix budget without assuming finiteness of the filtration.
-- source:
--   Third source-exact reduction for original stopped physical-grid process, complementing Proved 204f43a5 selector and 5319a1cb predictability, and supplying Measurable k required by Proved 2b993cd3 original bounded predictable source-prefix signed budget.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_nat_prefix_masks_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : Ω → ℕ)
    (hPrefix : ∀ i : ℕ, MeasurableSet {ω : Ω | i < k ω}) :
    Measurable k := by sorry
