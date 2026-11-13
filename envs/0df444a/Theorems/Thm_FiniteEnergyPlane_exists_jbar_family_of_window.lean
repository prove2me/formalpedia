-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jbar_family_of_window
-- name    : FiniteEnergyPlane.exists_jbar_family_of_window
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-12T18:10:21.644588+00:00
-- url     : https://prove2.me/theorems/dc421054-ea81-41c8-8626-e7078beb2747
-- title:
--   Families of $\bar J$-holomorphic planes near $\mathbb{C}\times\{0\}$ for a standard tube structure
-- statement:
--   Let $\rho, b > 0$ and let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`): $\bar J$ is a smooth almost complex structure on $\mathbb{C} \times B_\rho(0)$, equal to $i \oplus i$ along $\mathbb{C} \times \{0\}$, asymptotically cylindrical at $z = \infty$ with $t$-periodic limit $J_\infty$, and $S_\infty$ is the symmetric loop of its normal linearization at $\infty$. Let $\delta < 0$ be a weight such that $\delta$ is not an eigenvalue of the asymptotic operator $A_\infty = -J_0\partial_t - S_\infty$ on loops, every eigenvalue $\mu < \delta$ has eigenfunctions of winding $\le 0$, and every eigenvalue $\mu > \delta$ has eigenfunctions of winding $\ge 1$ (`IsLoopEigen`, `HasLoopEigenWind`).
--
--   Then for every $l \ge 1$ and every $w_0 \in \mathbb{C}$ there are $r > 0$ and a map $G : \mathbb{C} \times \mathbb{R} \to \mathbb{C} \times \mathbb{C}$, $C^l$ on $\mathbb{C} \times (-r, r)$, with
--   - $G(z, 0) = (z, 0)$ for all $z$, and $\big[\partial_t G(0, 0)\big]_2 = w_0$;
--   - for each $t \in (-r, r)$, the map $G_t = G(\cdot, t) = (\psi_t, v_t)$ is $C^\infty$, takes values in $\mathbb{C} \times B_\rho(0)$, is $\bar J$-holomorphic on $\mathbb{C}$, and satisfies, for some constants $C$ and $\beta > 0$ (depending on $t$),
--   $$|\psi_t(z) - z| \le C(1+|z|)^{1-\beta}, \qquad |v_t(z)| \le C(1+|z|)^{\delta/2\pi},$$
--   and for every $z$ there is $\Delta \in \mathbb{C}$ with $\big[DG(z,t)(\Delta, 1)\big]_1 = 0$ and $\big|\big[DG(z,t)(\Delta,1)\big]_2\big| \le C(1+|z|)^{\delta/2\pi}$;
--   - for every $\varepsilon > 0$ there is $r' \in (0, r]$ such that for $|t| < r'$ and all $z$:
--   $$|\psi_t(z) - z| \le \varepsilon(1+|z|), \quad |v_t(z)| \le \varepsilon, \quad \|D\psi_t(z) - \mathrm{id}\| \le \varepsilon, \quad (1+|z|)\,\|Dv_t(z)\| \le \varepsilon.$$
--
--   **Role.** $\mathbb{C} \times \{0\}$ is a $\bar J$-holomorphic plane, and the statement produces nearby $\bar J$-holomorphic planes in every normal direction at $z = 0$, with the asymptotic control at $\infty$ given by the window at $\delta$. Through a standard tube around a fast finite-energy plane, this gives the local families of fast planes in Hryniewicz's Lemmas 6.10 and 6.20. The statement involves no Reeb dynamics.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For a standard tube structure `Jbar` whose asymptotic loop `Sinf` has a winding window at a
negative weight `δ` (`δ` is not an eigenvalue; eigenvalues below `δ` have winding `≤ 0`, those above
have winding `≥ 1`), every `w₀ ∈ ℂ` is the normal velocity at `z = 0` of a `C^l` one-parameter
family `G(·, t)` of `Jbar`-holomorphic planes through `G(·, 0) = (z, 0)`: each member is smooth,
stays in `ℂ × ball 0 ρ`, has tangential part `z + O((1+‖z‖)^{1-β})` and normal part
`O((1+‖z‖)^{δ/2π})` with a `t`-derivative of the same order, and the members converge to
`(z, 0)` in weighted `C¹` as `t → 0`. -/
theorem exists_jbar_family_of_window (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) (w₀ : ℂ) :
    ∃ r > 0, ∃ G : ℂ × ℝ → ℂ × ℂ, ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, G (z, 0) = (z, 0)) ∧ (fderiv ℝ G (0, 0) (0, 1)).2 = w₀ ∧
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
