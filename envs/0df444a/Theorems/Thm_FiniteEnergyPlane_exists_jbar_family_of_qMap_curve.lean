-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jbar_family_of_qMap_curve
-- name    : FiniteEnergyPlane.exists_jbar_family_of_qMap_curve
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-12T18:10:22.5266+00:00
-- url     : https://prove2.me/theorems/a3e8526f-e405-4790-8bce-97009e8a209b
-- title:
--   Curves of zeros of the weighted operator give families of $\bar J$-holomorphic planes
-- statement:
--   Let $\rho, b > 0$, let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`), let $\delta < 0$ and $\delta_T \in (\max(\delta, -2\pi), 0)$, let $\chi_T, \chi_N, \beta$ satisfy `IsSlopeWeight χT π (2π + δT)`, `IsSlopeWeight χN π δ` and `IsLeftCutoff β`, and let $l \in \mathbb{N}$. Then there is $\varepsilon_0 > 0$ with the following property.
--
--   Let $r > 0$ and let $\gamma : \mathbb{R} \to W^{1,4} \times \mathbb{C} \times W^{1,4}$ be $C^\infty$ on $(-r, r)$, with $\gamma(0) = 0$, $\gamma'(0) = k$, and, for every $t \in (-r, r)$, $\gamma(t) \in B_{\varepsilon_0}(0)$ and `qMap Jbar χT χN β (γ t) = 0`. Then there are $r_1 > 0$ and $G : \mathbb{C} \times \mathbb{R} \to \mathbb{C} \times \mathbb{C}$, $C^l$ on $\mathbb{C} \times (-r_1, r_1)$, such that
--   - $G(z, 0) = (z, 0)$ for all $z$, and $\big[\partial_t G(0,0)\big]_2 = k_2$, the $\mathbb{C}$-component of $k$;
--   - for each $t \in (-r_1, r_1)$ the map $G_t = (\psi_t, v_t)$ is $C^\infty$, takes values in $\mathbb{C} \times B_\rho(0)$, is $\bar J$-holomorphic on $\mathbb{C}$, and satisfies, for some $C$ and $\beta' > 0$, $|\psi_t(z) - z| \le C(1+|z|)^{1-\beta'}$, $|v_t(z)| \le C(1+|z|)^{\delta/2\pi}$, and for every $z$ there is $\Delta$ with $\big[DG(z,t)(\Delta,1)\big]_1 = 0$ and $\big|\big[DG(z,t)(\Delta,1)\big]_2\big| \le C(1+|z|)^{\delta/2\pi}$;
--   - for every $\varepsilon > 0$ there is $r' \in (0, r_1]$ such that for $|t| < r'$ and all $z$: $|\psi_t(z) - z| \le \varepsilon(1+|z|)$, $|v_t(z)| \le \varepsilon$, $\|D\psi_t(z) - \mathrm{id}\| \le \varepsilon$ and $(1+|z|)\|Dv_t(z)\| \le \varepsilon$.
--
--   The hypothesis that **every** member $\gamma(t)$ is a zero is essential.
--
--   **Role.** Weak solutions of the $\bar J$-Cauchy–Riemann equation in weighted Sobolev coordinates are turned into an honest family of smooth $\bar J$-holomorphic planes, jointly regular in the parameter, with pointwise weighted bounds.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For a standard tube structure there is `ε₀ > 0` such that every `C^∞` curve `γ` of zeros of
`qMap` in `ball 0 ε₀` (every member a zero) with `γ 0 = 0` and velocity `k` at `0` defines a jointly
`C^l` family `G(·, t)` of `Jbar`-holomorphic planes through `G(·, 0) = (z, 0)`, with normal
velocity `k.2.1` at `z = 0`, the weighted bounds on each member, and weighted `C¹` convergence to
`(z, 0)` as `t → 0`. -/
theorem exists_jbar_family_of_qMap_curve (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) (l : ℕ) :
    ∃ ε₀ > 0, ∀ r > 0, ∀ (γ : ℝ → QDom) (k : QDom), ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) →
      γ 0 = 0 → HasDerivAt γ k 0 →
      (∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε₀ ∧ qMap Jbar χT χN β (γ t) = 0) →
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = k.2.1 ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
