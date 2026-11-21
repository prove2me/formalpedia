-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_ne_shiftA_of_forall_norm_lt
-- name    : FiniteEnergyPlane.forall_ne_shiftA_of_forall_norm_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:13:56.436494+00:00
-- url     : https://prove2.me/theorems/493bb8ab-9f4a-44f2-b6f2-87038fee71c2
-- title:
--   No intersections with translates beyond an exceptional level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and let $\tilde u,\tilde v:\mathbb{C}\to\mathbb{R}^4$ be fast finite-energy planes that are immersions. For $\tau\in\mathbb{R}$ write $\tau\cdot\tilde v=e^{2\tau}\tilde v$ for the translate of $\tilde v$ by $\tau$ in the $\mathbb{R}$-direction of the symplectization. Let $\tau_0\in\mathbb{R}$ be such that for every $\varepsilon>0$ there is $R$ with
--   $$\tilde u(z)=(\tau\cdot\tilde v)(w),\ |\tau-\tau_0|\ge\varepsilon\ \Longrightarrow\ |z|<R\text{ and }|w|<R .$$
--   Then $\tilde u(z)\neq(\tau\cdot\tilde v)(w)$ for all $\tau>\tau_0$ and all $z,w\in\mathbb{C}$.
--
--   Role: from a bound on where intersections with translates can occur to the absence of intersections with all translates on one side of $\tau_0$; applied with $\tilde u,\tilde v$ swapped (and $-\tau_0$) it covers the other side.
--
--   **Formalization Note** $\tau\cdot\tilde v$ is `shiftA τ v`. "Fast" is `IsFastPlane`; "immersion" means `fderiv ℝ u z` is injective for every $z$. No asymptotic orbit is fixed in the statement, and $\tilde u=\tilde v$ is allowed.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 4.11

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Translations of one immersed fast plane against another. Let `u, v` be fast finite-energy
planes that are immersions, and let `τ₀ ∈ ℝ` be such that for every `ε > 0` the intersections
`u z = (τ · v)(w)` with `|τ - τ₀| ≥ ε` all have `z, w` in a fixed ball. Then `u` meets no
translate `τ · v = shiftA τ v` with `τ > τ₀`. -/
theorem forall_ne_shiftA_of_forall_norm_lt (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (hv : IsFastPlane H J v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (τ₀ : ℝ)
    (hF : ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R) :
    ∀ τ > τ₀, ∀ z w : ℂ, u z ≠ shiftA τ v w := by
  sorry

end FiniteEnergyPlane
