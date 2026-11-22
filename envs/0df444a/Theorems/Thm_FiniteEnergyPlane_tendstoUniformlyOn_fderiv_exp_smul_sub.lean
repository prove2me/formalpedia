-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoUniformlyOn_fderiv_exp_smul_sub
-- name    : FiniteEnergyPlane.tendstoUniformlyOn_fderiv_exp_smul_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:09:22.842041+00:00
-- url     : https://prove2.me/theorems/ba8b23f7-70ca-4380-b3c2-796ff4df4cce
-- title:
--   C^1-smallness of translated differences of a locally convergent sequence
-- statement:
--   Let $u_0,v_k:\mathbb{C}\to\mathbb{R}^4$ be $C^1$ maps with $v_k\to u_0$ in $C^\infty_{loc}(\mathbb{C})$, and $t_0\in\mathbb{R}$. Put $h_k(s,z,t)=e^{2s}\,(v_k(z)-u_0(z))$ on $\mathbb{R}\times\mathbb{C}\times\mathbb{R}$. Then every $h_k$ is differentiable, $h_k(0,0,t_0)\to0$, and $Dh_k\to0$ uniformly on the unit ball around $(0,0,t_0)$.
--
--   The $\mathbb{R}$-translated differences of a $C^\infty_{loc}$-convergent sequence are $C^1$-small near a point. It is used to locate intersections of Reeb trajectories with nearby planes (Hryniewicz 2012, Lemmas 7.2 and 7.3).
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`; $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ`; uniform convergence of the derivatives is `TendstoUniformlyOn` on `ball (0, 0, t₀) 1` (sup norm on the product).
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemmas 7.2 and 7.3

import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Metric Filter Topology

/-- Let `u₀, vₖ : ℂ → V 1` be `C¹` with `vₖ → u₀` in `C^∞_loc(ℂ)`, and `t₀ ∈ ℝ`. The maps
`hₖ(s, z, t) = e^{2s} (vₖ(z) - u₀(z))` on `ℝ × ℂ × ℝ` are differentiable, `hₖ(0, 0, t₀) → 0`, and
`Dhₖ → 0` uniformly on the unit ball around `(0, 0, t₀)`. -/
theorem tendstoUniformlyOn_fderiv_exp_smul_sub (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀)
    (v : ℕ → ℂ → V 1) (hv : ∀ k, ContDiff ℝ 1 (v k))
    (hlim : JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ) (t₀ : ℝ) :
    (∀ k, ∀ q : ℝ × ℂ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) ∧
    Tendsto (fun k => Real.exp (2 * (0 : ℝ)) • (v k (0 : ℂ) - u₀ 0)) atTop (𝓝 0) ∧
    TendstoUniformlyOn (fun k q => fderiv ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) 0 atTop
      (ball ((0 : ℝ), (0 : ℂ), t₀) 1) := by
  sorry

end FiniteEnergyPlane
