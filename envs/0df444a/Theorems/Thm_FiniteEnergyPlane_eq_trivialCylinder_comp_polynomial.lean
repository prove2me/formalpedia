-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_comp_polynomial
-- name    : FiniteEnergyPlane.eq_trivialCylinder_comp_polynomial
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:24:39.895279+00:00
-- url     : https://prove2.me/theorems/0011475c-c463-40b7-a018-a8563b9bee9e
-- title:
--   Finite-energy curves with vanishing $d\lambda$-energy and negative punctures are trivial cylinders composed with polynomials
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $\Gamma\subset\mathbb{C}$ finite, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ such that $a(u(z))\to-\infty$ as $z\to z_0$ for every $z_0\in\Gamma$. If $\int_{\mathbb{C}\setminus\Gamma}u^*d\lambda_0=0$, then there are a polynomial $p$ of degree $\ge1$ with zero set exactly $\Gamma$ and a periodic Reeb orbit $P$ such that $u=F_P\circ p$ on $\mathbb{C}\setminus\Gamma$.
--
--   **Formalization Note** Hryniewicz writes $F_P(e^{2\pi(s+it)})=(Ts,x(Tt))$ in $\mathbb{R}\times S$; in the coordinate $y=e^{2a}x$ this is `trivialCylinder P`, $F_P(w)=|w|^{T/\pi}x(T\arg w/2\pi)$. "Nonconstant" is an explicit hypothesis; Hryniewicz's finite-energy surfaces are nonconstant by convention. The punctures are approached along `𝓝[≠] z₀`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.18 (Hofer, Wysocki and Zehnder), p. 12

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder: Hryniewicz 2014, Theorem 2.18. Let `Γ ⊆ ℂ` be finite and `u` a
nonconstant finite-energy `J̃`-holomorphic curve on `ℂ \ Γ` all of whose punctures in `Γ` are
negative (`a → -∞`). If its `dλ`-energy vanishes, there are a nonconstant polynomial `p` with zero
set `Γ` and a periodic Reeb orbit `P` such that `u = F_P ∘ p` on `ℂ \ Γ`, where `F_P` is the trivial
cylinder over `P`. (Hryniewicz's `F_P(e^{2π(s+it)}) = (Ts, x(Tt))` reads `F_P(w) = |w|^{T/π} x(T arg w / 2π)`
in the coordinate `y = e^{2a} x`. "Nonconstant" is explicit here; it is implicit in his
"finite-energy surface".) -/
theorem eq_trivialCylinder_comp_polynomial {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u)
    (hnc : ∃ z₁ ∉ Γ, ∃ z₂ ∉ Γ, u z₁ ≠ u z₂)
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => aCoord H (u z)) (𝓝[≠] z₀) atBot)
    (hzero : dlambdaEnergy H (↑Γ)ᶜ u = 0) :
    ∃ p : Polynomial ℂ, 0 < p.natDegree ∧ {z | p.eval z = 0} = ↑Γ ∧
      ∃ P : ReebOrbit H, ∀ z ∉ Γ, u z = trivialCylinder P (p.eval z) := by
  sorry

end FiniteEnergyPlane
