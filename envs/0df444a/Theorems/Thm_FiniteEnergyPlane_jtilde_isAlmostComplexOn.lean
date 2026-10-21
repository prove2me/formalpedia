-- Prove2me | Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
-- name    : FiniteEnergyPlane.jtilde_isAlmostComplexOn
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:22:09.249844+00:00
-- url     : https://prove2.me/theorems/b906cc6d-8009-445f-8a5c-b2689d1a887e
-- title:
--   The symplectization structure $\tilde J$ is a smooth almost complex structure invariant under radial scaling
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Then $\tilde J$ is a $C^\infty$ almost complex structure on $V\setminus\{0\}$, the maps $\mathrm{proj}$ and $a$ are $C^\infty$ on $V\setminus\{0\}$, every $y\neq0$ satisfies $H(\mathrm{proj}(y))=1$ and $y=e^{2a(y)}\mathrm{proj}(y)$, and $\tilde J(cy)=\tilde J(y)$ for $y\neq0$ and $c>0$.
--
--   **Formalization Note** The first claim is `JHolomorphic.IsAlmostComplexOn (Jtilde H J) {y | y ≠ 0}` (smoothness on the open set and $\tilde J(y)^2=-1$ there). Smoothness of `proj H` and `aCoord H` is `ContDiffOn ℝ ∞` on `{y | y ≠ 0}`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The symplectization structure (Hryniewicz 2014, § 2.2; Hofer 1993, § 3). On `V n \ {0}` the
map `J̃` is a smooth almost complex structure, and it is invariant under the radial scaling
`y ↦ c y`, `c > 0` (the `ℝ`-action on `ℝ × S`). The radial projection to `S` and the coordinate
`a` are smooth on `V n \ {0}`, and `y = e^{2a(y)} proj(y)` with `proj(y) ∈ S`. -/
theorem jtilde_isAlmostComplexOn {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) :
    JHolomorphic.IsAlmostComplexOn (Jtilde H J) {y | y ≠ 0} ∧
      ContDiffOn ℝ ∞ (proj H) {y | y ≠ 0} ∧ ContDiffOn ℝ ∞ (aCoord H) {y | y ≠ 0} ∧
      (∀ y : V n, y ≠ 0 → H (proj H y) = 1 ∧ y = Real.exp (2 * aCoord H y) • proj H y) ∧
      ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c → Jtilde H J (c • y) = Jtilde H J y := by
  sorry

end FiniteEnergyPlane
