-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_page_direction_of_hasAsymptoticEigenvector
-- name    : FiniteEnergyPlane.exists_page_direction_of_hasAsymptoticEigenvector
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T13:02:43.369421+00:00
-- url     : https://prove2.me/theorems/87bebfe8-188e-40d8-a0fb-12e47d0f150a
-- title:
--   The end of a plane with an asymptotic eigenvector meets every ray of the tube
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, and $P = (x, T)$ a periodic Reeb orbit. Let $u : \mathbb{C} \to \mathbb{R}^4$ have an asymptotic eigenvector $v$ with eigenvalue $\mu$ at the positive puncture $\infty$, over $P$ (Hryniewicz, Theorem 2.11). Let $Z$ be a unitary frame of $\xi$ along $P$, and consider the tube map $(\tau, a) \mapsto \mathrm{proj}(x(\tau) + Z(\tau/T)\,a)$.
--
--   Then $v = Z E$ for a continuous, $1$-periodic, nowhere vanishing $E : \mathbb{R} \to \mathbb{R}^2$. Moreover, there are $\rho_0 > 0$ and a map $\omega : \mathbb{R} \times \mathbb{R} \to \mathbb{R}^2$, continuous on $\mathbb{R} \times (0, \rho_0)$, with the following properties.
--   - For every $\tau \in \mathbb{R}$ and $\rho \in (0, \rho_0)$, $|\omega(\tau, \rho)| = 1$ and the tube point $\mathrm{proj}(x(\tau) + Z(\tau/T)\,\rho\,\omega(\tau,\rho))$ lies in $\mathrm{proj}(u(\mathbb{C}))$.
--   - The direction $\omega$ tends to the direction of $E$, uniformly. For every $\varepsilon > 0$ there are $\rho_1 > 0$ and $\delta > 0$ such that $|\omega(\tau, \rho) - E(\tau'/T)/|E(\tau'/T)|| < \varepsilon$ whenever $|\tau - \tau'| < \delta$ and $0 < \rho < \rho_1$.
--
--   Role: near the asymptotic orbit, the image of the end of $u$ in $S$ meets every ray of the tube, and its direction is controlled by the asymptotic eigenvector.
--
--   Formalization Note: `HasAsymptoticEigenvector H J u cylInf P 1 μ v` is Hryniewicz's Theorem 2.11 representation of the end of $u$ at $\infty$ in the tube $(\tau, h) \mapsto \mathrm{proj}(x(\tau) + h)$. Vectors of $\mathbb{R}^2$ are `CauchyRiemannIndex.Vec 1`. The direction map $\omega$ is `dir`, a function of the pair $(\tau, \rho)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Near the orbit, the end of `u` meets every ray of the tube in a direction that is
continuous and tends to the direction of the asymptotic eigenvector. -/
theorem exists_page_direction_of_hasAsymptoticEigenvector (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (u : ℂ → V 1) (μ : ℝ) (v : ℝ → V 1) (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z) :
    ∃ E : ℝ → CauchyRiemannIndex.Vec 1, Continuous E ∧ Function.Periodic E 1 ∧
      (∀ t : ℝ, E t ≠ 0) ∧ (∀ t : ℝ, v t = Z t (E t)) ∧
      ∃ ρ₀ > 0, ∃ dir : ℝ × ℝ → CauchyRiemannIndex.Vec 1,
        ContinuousOn dir (Set.univ ×ˢ Set.Ioo 0 ρ₀) ∧
        (∀ τ : ℝ, ∀ ρ ∈ Set.Ioo 0 ρ₀, ‖dir (τ, ρ)‖ = 1 ∧
          proj H (P.x τ + Z (τ / P.T) (ρ • dir (τ, ρ))) ∈ Set.range (fun z => proj H (u z))) ∧
        ∀ ε > 0, ∃ ρ₁ > 0, ∃ δ > 0, ∀ τ τ' : ℝ, |τ - τ'| < δ → ∀ ρ ∈ Set.Ioo 0 ρ₁,
          ‖dir (τ, ρ) - ‖E (τ' / P.T)‖⁻¹ • E (τ' / P.T)‖ < ε := by
  sorry

end FiniteEnergyPlane
