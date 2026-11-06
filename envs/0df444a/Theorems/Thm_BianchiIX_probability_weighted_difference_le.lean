-- Prove2me | Theorems.Thm_BianchiIX_probability_weighted_difference_le
-- name    : BianchiIX.probability_weighted_difference_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:10:46.907434+00:00
-- url     : https://prove2.me/theorems/bd05e3a5-4c04-4d51-bd3a-08772119188b
-- title:
--   A bound for differences of weighted probability averages
-- statement:
--   Let $I$ be a set and let $p,q:I\to\mathbb R$
--   be nonnegative probability masses:
--   $$\sum_{i\in I}p_i=\sum_{i\in I}q_i=1.$$
--   The sums are unordered convergent sums.
--
--   If $|f_i|\leq M$ for all $i$, then
--   $$\left|\sum_i p_if_i-\sum_iq_if_i\right|
--   \leq M\sum_i|p_i-q_i|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/DiscreteMass.lean#L55-L75

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.probability_weighted_difference_le {ι : Type*} {p q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1)
    (hf : ∀ i, |f i| ≤ M) :
    |(∑' i, p i * f i) - ∑' i, q i * f i| ≤ M * ∑' i, |p i - q i| := by sorry
