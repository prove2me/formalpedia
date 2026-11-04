-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_hasEigenWind
-- name    : FiniteEnergyPlane.exists_hasWindInfAt_hasEigenWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:39:10.909475+00:00
-- url     : https://prove2.me/theorems/e03d53a9-e985-42e3-9b48-678cde398234
-- title:
--   Bounds for $\mathrm{wind}_\infty$ at a nondegenerate puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u$ be a finite-energy $\tilde J$-holomorphic curve on $B_r(z_0)\setminus\{z_0\}$ such that $z_0$ is a nondegenerate puncture (Hryniewicz, Definition 2.9) of sign $\varepsilon=\pm1$ with asymptotic limit $P$, and $\pi\,du$ does not vanish identically on any punctured neighbourhood of $z_0$. Then $\mathrm{wind}_\infty$ of $u$ at $z_0$ is the winding of an eigenvalue $\mu$ of $A_P$ with $\varepsilon\mu<0$. In particular $\mathrm{wind}_\infty\le\alpha^-(P)$ if $\varepsilon=1$ and $\mathrm{wind}_\infty\ge\alpha^+(P)$ if $\varepsilon=-1$.
--
--   **Formalization Note** $P$ need not be nondegenerate. "Not identically zero near $z_0$" is: every $B_\rho(z_0)\setminus\{z_0\}$ contains $z$ with `dlambdaDensity H u z ≠ 0`. The bounds are stated for every `a` with `IsAlphaMinus J P a` and every `b` with `IsAlphaPlus J P b`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `z₀` be a puncture of sign `ε` of a finite-energy `J̃`-holomorphic curve `u`, nondegenerate
in the sense of Definition 2.9 with asymptotic limit `P`, near which `π du` does not vanish
identically. Then `wind_∞` of `u` at `z₀` is the winding number of an eigenvalue `μ` of `A_P` with
`εμ < 0`. In particular `wind_∞ ≤ α⁻(P)` at a positive puncture and `wind_∞ ≥ α⁺(P)` at a negative one. -/
theorem exists_hasWindInfAt_hasEigenWind (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (ball z₀ r \ {z₀}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u (cylEndAt z₀) P ε)
    (hne : ∀ ρ > 0, ∃ z ∈ ball z₀ ρ \ {z₀}, dlambdaDensity H u z ≠ 0) :
    ∃ (k : ℤ) (μ : ℝ), ε * μ < 0 ∧ HasEigenWind J P μ k ∧ HasWindInfAt H u (cylEndAt z₀) ε k ∧
      (ε = 1 → ∀ a : ℤ, IsAlphaMinus J P a → k ≤ a) ∧
      (ε = -1 → ∀ b : ℤ, IsAlphaPlus J P b → b ≤ k) := by
  sorry

end FiniteEnergyPlane
