-- Prove2me | Theorems.Thm_BianchiIX_probability_mass_l1_identity
-- name    : BianchiIX.probability_mass_l1_identity
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:07:43.202829+00:00
-- url     : https://prove2.me/theorems/de5be085-fdc1-4615-8a32-7eecd22ece34
-- title:
--   An overlap identity for discrete probability masses
-- statement:
--   Let $I$ be a set and let $p,q:I\to\mathbb R$
--   be nonnegative probability masses:
--   $$\sum_{i\in I}p_i=\sum_{i\in I}q_i=1.$$
--   The sums are unordered convergent sums.
--
--   $$\sum_{i\in I}|p_i-q_i|=2-2\sum_{i\in I}\min(p_i,q_i).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/DiscreteMass.lean#L19-L27

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open Filter
open scoped Topology
open BianchiIX

theorem BianchiIX.probability_mass_l1_identity {ι : Type*} {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1) :
    (∑' i, |p i - q i|) = 2 - 2 * ∑' i, min (p i) (q i) := by sorry
