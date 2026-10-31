-- Prove2me | Theorems.Thm_AubinLipschitz_ekeland_with_distance_bound
-- name    : AubinLipschitz.ekeland_with_distance_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:25.367288+00:00
-- url     : https://prove2.me/theorems/69631481-57b1-4760-93b9-1753d957d965
-- title:
--   §3, (11) — Ekeland's theorem with the distance estimate
-- statement:
--   Let $Z$ be a complete metric space, $f:Z\to\mathbb R$ lower semicontinuous and bounded below, $\varepsilon>0$ and $z_1\in Z$. Then there is $\bar z\in Z$ such that
--
--   $$
--   f(\bar z)+\varepsilon\, d(\bar z,z_1)\le f(z_1)
--   \qquad\text{and}\qquad
--   f(\bar z)\le f(z)+\varepsilon\, d(\bar z,z)\ \text{ for all } z\in Z.
--   $$
--
--   The first inequality is what bounds the distance from $\bar z$ to the starting point in the proof of Theorem 2 of §3.
--
--   Differences from the source:
--   - generalization: the continuous function V(x,y) = ‖y₂ − y‖ on graph(F) with the metric ‖x − x'‖ + ‖y − y'‖ → any lower semicontinuous bounded-below f on any complete metric space; reason: this is the cited theorem, and the instance Z = graph(F), z₁ = (x₁,y₁) gives (11).
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, display (11), p.25

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, display (11), p.25 (Ekeland's theorem, in the form applied there): for a complete
metric space `Z`, a lower semicontinuous `f : Z → ℝ` bounded below, `ε > 0` and `z₁ ∈ Z`, there
is `zbar` with `f(zbar) + ε d(zbar, z₁) ≤ f(z₁)` and `f(zbar) ≤ f(z) + ε d(zbar, z)` for all `z`. -/
theorem ekeland_with_distance_bound {Z : Type*} [MetricSpace Z] [CompleteSpace Z] (f : Z → ℝ)
    (hf : LowerSemicontinuous f) (m : ℝ) (hm : ∀ z, m ≤ f z) (ε : ℝ) (hε : 0 < ε) (z₁ : Z) :
    ∃ zbar : Z, f zbar + ε * dist zbar z₁ ≤ f z₁ ∧ ∀ z : Z, f zbar ≤ f z + ε * dist zbar z := by sorry

end AubinLipschitz
