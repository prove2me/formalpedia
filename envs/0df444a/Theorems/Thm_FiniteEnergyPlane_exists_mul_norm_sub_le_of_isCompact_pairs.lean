-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isCompact_pairs
-- name    : FiniteEnergyPlane.exists_mul_norm_sub_le_of_isCompact_pairs
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:36:24.925236+00:00
-- url     : https://prove2.me/theorems/52c87912-0c4d-465a-b4d9-1621f1df2e57
-- title:
--   Lower Lipschitz bound on a compact set of pairs
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $G : E \to F$ of class $C^1$ and $Q \subset E \times E$ compact. Suppose $G(x) \ne G(y)$ for every $(x, y) \in Q$ with $x \ne y$, and $DG(x)$ is injective for every $(x, x) \in Q$. Then there is $c > 0$ with $c \|x - y\| \le \|G(x) - G(y)\|$ for all $(x, y) \in Q$.
--
--   **Role.** Taking $Q = K \times K$ gives the uniform embedding bound for an injective immersion on a compact set $K$. Other choices of $Q$ cover maps that are injective only on part of the domain, such as periodic curves.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A `C¹` map on a finite-dimensional space that separates the off-diagonal pairs of a compact set
`Q` of pairs of points, and has injective derivative at the diagonal pairs of `Q`, satisfies a
uniform lower Lipschitz bound on `Q`. -/
theorem exists_mul_norm_sub_le_of_isCompact_pairs {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (hG : ContDiff ℝ 1 G) (Q : Set (E × E)) (hQ : IsCompact Q)
    (hne : ∀ p ∈ Q, p.1 ≠ p.2 → G p.1 ≠ G p.2)
    (hd : ∀ p ∈ Q, p.1 = p.2 → Function.Injective (fderiv ℝ G p.1)) :
    ∃ c > 0, ∀ p ∈ Q, c * ‖p.1 - p.2‖ ≤ ‖G p.1 - G p.2‖ := by
  sorry

end FiniteEnergyPlane
