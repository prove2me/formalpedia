-- Prove2me | Theorems.Thm_Convex_exists_continuous_retraction
-- name    : Convex.exists_continuous_retraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:25.671103+00:00
-- url     : https://prove2.me/theorems/0e3cdc0c-0c3e-457c-b487-7a9f62fe336c
-- title:
--   A nonempty complete convex set is a continuous retract of the space
-- statement:
--   Let $H$ be a real inner product space and let $K \subseteq H$ be nonempty, convex and
--   complete. Then $K$ is a continuous retract of the whole space: there exists
--   $p : H \to H$ with
--
--   1. $p$ continuous on $H$;
--   2. $p(x) \in K$ for every $x \in H$;
--   3. $p(x) = x$ for every $x \in K$.
--
--   In short, every point of the space can be moved into $K$ continuously, without disturbing the
--   points already there. This is the device that transfers fixed-point theorems from a ball to an
--   arbitrary closed convex set: composing a self-map of $K$ with $p$ extends it to a self-map of a
--   ball containing $K$, whose fixed points must already lie in $K$. Completeness, rather than
--   compactness, is what the statement needs.
-- source:
--   J.-P. Aubin and I. Ekeland, Applied Nonlinear Analysis, Wiley 1984, §1.4 (projection onto a closed convex set). Carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Convex.exists_continuous_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by sorry
