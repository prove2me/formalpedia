-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoUniformlyOn_fderiv_exp_smul_sub_of_tendstoUniformlyOn
-- name    : FiniteEnergyPlane.tendstoUniformlyOn_fderiv_exp_smul_sub_of_tendstoUniformlyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:30:20.751316+00:00
-- url     : https://prove2.me/theorems/fe27f0c4-b66d-4556-8088-4481f710fac2
-- title:
--   C^1-smallness of translated differences of a C^1-convergent sequence
-- statement:
--   Let $u_0,v_k:\mathbb{C}\to\mathbb{R}^4$ be $C^1$ maps with $v_k\to u_0$ and $Dv_k\to Du_0$ uniformly on the closed unit disc, and $t_0\in\mathbb{R}$. Put $h_k(s,z,t)=e^{2s}\,(v_k(z)-u_0(z))$ on $\mathbb{R}\times\mathbb{C}\times\mathbb{R}$. Then every $h_k$ is differentiable, $h_k(0,0,t_0)\to0$, and $Dh_k\to0$ uniformly on the unit ball around $(0,0,t_0)$.
--
--   The $\mathbb{R}$-translated differences of a sequence converging in $C^1$ near $0$ are $C^1$-small near a point. It is the $C^1$ counterpart of the corresponding statement for $C^\infty_{loc}$-convergent sequences and is used to locate intersections of Reeb trajectories with the leaves of a $C^1$ family (Hryniewicz 2012, Lemma 7.2).
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`; uniform convergence of values and derivatives is `TendstoUniformlyOn` on `closedBall 0 1`; the conclusion uses the sup norm on the product $\mathbb{R}\times\mathbb{C}\times\mathbb{R}$ and the ball `ball (0, 0, t₀) 1`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u₀, vₖ : ℂ → V 1` be `C¹` with `vₖ → u₀` and `Dvₖ → Du₀` uniformly on the closed unit
disc. Put `hₖ(s, z, t) = e^{2s} (vₖ(z) - u₀(z))`. Then every `hₖ` is differentiable,
`hₖ(0, 0, t₀) → 0`, and `Dhₖ → 0` uniformly on the unit ball around `(0, 0, t₀)`. -/
theorem tendstoUniformlyOn_fderiv_exp_smul_sub_of_tendstoUniformlyOn (u₀ : ℂ → V 1)
    (hu₀ : ContDiff ℝ 1 u₀) (v : ℕ → ℂ → V 1) (hv : ∀ k, ContDiff ℝ 1 (v k))
    (h0u : TendstoUniformlyOn v u₀ atTop (closedBall 0 1))
    (h1u : TendstoUniformlyOn (fun k => fderiv ℝ (v k)) (fderiv ℝ u₀) atTop (closedBall 0 1))
    (t₀ : ℝ) :
    (∀ k, ∀ q : ℝ × ℂ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) ∧
    Tendsto (fun k => Real.exp (2 * (0 : ℝ)) • (v k (0 : ℂ) - u₀ 0)) atTop (𝓝 0) ∧
    TendstoUniformlyOn (fun k q => fderiv ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) 0 atTop
      (ball ((0 : ℝ), (0 : ℂ), t₀) 1) := by
  sorry

end FiniteEnergyPlane
