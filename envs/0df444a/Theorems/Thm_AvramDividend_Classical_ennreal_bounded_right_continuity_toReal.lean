-- Prove2me | Theorems.Thm_AvramDividend_Classical_ennreal_bounded_right_continuity_toReal
-- name    : AvramDividend.Classical.ennreal_bounded_right_continuity_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:02:40.036285+00:00
-- url     : https://prove2.me/theorems/64005f6d-0ee7-4127-be42-f0c1068ddb10
-- title:
--   Uniformly bounded ENNReal right-continuous kernels remain right-continuous after toReal
-- statement:
--   Let F be an ENNReal-valued function on the real line, right-continuous at every point and uniformly bounded above by one. Then the real-valued function obtained by ENNReal.toReal∘F is also right-continuous everywhere. The uniform bound ensures the discontinuity of toReal at infinity cannot occur.
-- source:
--   Use Mathlib `ne_top_of_le_ne_top` with `ENNReal.one_ne_top` to show every value is finite; then compose the supplied right-continuity with pinned `ENNReal.continuousAt_toReal`. Needed to construct a real-valued Stieltjes CDF from the already-Proved infinite-horizon Esscher survival ENNReal infimum.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.BoundedOrder.Basic

open Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.ennreal_bounded_right_continuity_toReal
    (F : ℝ → ℝ≥0∞)
    (hright : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x)
    (hbound : ∀ x : ℝ, F x ≤ 1) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y : ℝ => (F y).toReal) (Ici x) x := by sorry
