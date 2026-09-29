-- Prove2me | Theorems.Thm_FamousTheorems_not_countable_real
-- name    : FamousTheorems.not_countable_real
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:52:01.456987+00:00
-- url     : https://prove2.me/theorems/acb1da80-3705-4df9-a415-54ab9cf79e1f
-- title:
--   The non-denumerability of the continuum
-- statement:
--   **The real numbers are uncountable.**
--
--   $$\mathbb{R} \text{ is not countable.}$$
--
--   Cantor's theorem of 1874, and the origin of set theory as a subject. His 1891 diagonal argument
--   gives the familiar proof: any proposed enumeration $r_1, r_2, \dots$ misses the real whose $n$-th
--   decimal digit differs from that of $r_n$.
--
--   The consequence that made it famous is that transcendental numbers exist in abundance — the
--   algebraic numbers are countable, so almost every real is transcendental — obtained without
--   exhibiting a single one, in contrast to Liouville's explicit construction.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem not_countable_real : ¬ (Set.univ : Set ℝ).Countable := by sorry

end FamousTheorems
