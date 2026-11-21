-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_eq_or_forall_ne_of_complexGraph
-- name    : FiniteEnergyPlane.forall_eq_or_forall_ne_of_complexGraph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T22:23:01.386743+00:00
-- url     : https://prove2.me/theorems/3d23a20f-9391-4299-95c2-94ea391a08c5
-- title:
--   Equal-or-disjoint dichotomy for a holomorphic graph and a complex graph in a standard tube
-- statement:
--   Let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure of radius $\rho$ and rate $b > 0$ on $\mathbb{C} \times \mathbb{C}$, and let $\delta < 0$ be such that every loop eigenfunction of the asymptotic operator of $S_\infty$ with eigenvalue $\mu \le \delta$ has winding number at most $0$. Let $g : \mathbb{C} \to B_\rho(0)$ be smooth, with $\bar J$-complex graph $x \mapsto (x, g(x))$ (that is, $\bar J$ maps each tangent space of the graph to itself), and with $g(e^{2\pi(s+it)})$ decaying like $e^{\delta s}$ in $C^\infty$. Let $\psi, v : \mathbb{C} \to \mathbb{C}$ be smooth with $v$ valued in $B_\rho(0)$, such that $z \mapsto (\psi(z), v(z))$ is $\bar J$-holomorphic, $\psi(z)/z - \kappa$ decays like $e^{-b's}$ in $C^\infty$ for some $\kappa \ne 0$ and $b' > 0$, and $v(e^{2\pi(s+it)})$ decays like $e^{\delta s}$ in $C^\infty$. Then either $v(z) = g(\psi(z))$ for all $z$, or $v(z) \ne g(\psi(z))$ for all $z$.
--
--   Role: two $\bar J$-complex surfaces in a standard tube, both converging to the zero section at the puncture fast enough, one parametrized as a graph over the base and the other by a holomorphic map, are either equal or disjoint.
--
--   Formalization Note: $e^{2\pi(s+it)}$ is `cylInf s t`; decay is `ExpDecayCInfty` (rate $-\delta$ means growth bound $e^{\delta s}$); the winding hypothesis is stated with `HasLoopEigenWind`; holomorphicity is `D(ψ, v) ∘ i = J̄ ∘ D(ψ, v)`, and complexity of the graph of `g` is stated componentwise.
-- source:
--   Standard tube structures in the theory of fast finite-energy planes; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A holomorphic graph `z ↦ (ψ z, v z)` for a standard tube structure `Jbar`, with `ψ`
asymptotic to `z ↦ κ z` and `v` decaying like `e^{δ s}` in cylindrical coordinates, and a smooth
function `g` with values in `ball 0 ρ` whose graph `x ↦ (x, g x)` is `Jbar`-complex and decays
like `e^{δ s}`, where the loop eigenfunctions of `Sinf` with eigenvalue at most `δ` have winding
at most `0`: the first graph either lies on the graph of `g` everywhere or nowhere. -/
theorem forall_eq_or_forall_ne_of_complexGraph (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v z = g (ψ z)) ∨ ∀ z, v z ≠ g (ψ z) := by
  sorry

end FiniteEnergyPlane
