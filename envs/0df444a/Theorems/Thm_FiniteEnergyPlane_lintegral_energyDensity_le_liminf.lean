-- Prove2me | Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_le_liminf
-- name    : FiniteEnergyPlane.lintegral_energyDensity_le_liminf
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T18:17:25.627407+00:00
-- url     : https://prove2.me/theorems/3ded3010-06da-4665-8321-d00e5a06ab3c
-- title:
--   Lower semicontinuity of energy integrals under pointwise $C^1$ convergence in a symplectization
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $W\subseteq\mathbb C$ open. Let $w$ and $v_k$ ($k\in\mathbb N$) be maps $\mathbb C\to\mathbb R^{2n+2}$ such that $w$ is $C^1$ on $W$ with $w(W)\subseteq\mathbb R^{2n+2}\setminus\{0\}$, for all large $k$ the map $v_k$ is $C^1$ on $W$ with $v_k(W)\subseteq\mathbb R^{2n+2}\setminus\{0\}$, and for every $z\in W$
--   $$v_k(z)\to w(z),\qquad Dv_k(z)\to Dw(z).$$
--   Then for every $C^1$ function $\varphi:\mathbb R\to\mathbb R$,
--   $$\int_W\big(w^*d(\varphi(a)\lambda)\big)^+\ \le\ \liminf_{k\to\infty}\int_W\big(v_k^*d(\varphi(a)\lambda)\big)^+ ,$$
--   where $(\cdot)^+$ is the positive part of the integrand with respect to $ds\wedge dt$.
--
--   For $\varphi\equiv1$ the integrand is the $d\lambda$-density, so the statement includes the lower semicontinuity of the $d\lambda$-energy.
--
--   **Formalization Note** The integrand is `energyDensity H φ`, in the coordinates $a=$ `aCoord H` and $w=$ `proj H`, and the integral is the lower integral `∫⁻ z in W, ENNReal.ofReal (energyDensity H φ v z)`. The pointwise convergence of $Dv_k(z)$ is in the operator norm. The compatible structure $J$ does not enter the conclusion.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Prop. 9.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Lower semicontinuity of the energy integrals under pointwise `C¹` convergence. Let `S` be a
strictly star-shaped level, `W ⊆ ℂ` open, and let `v_k, w` be `C¹` maps on `W` with values in
`ℝ^{2n+2} \ {0}` (for `v_k`: for all large `k`), such that `v_k(z) → w(z)` and `Dv_k(z) → Dw(z)`
for every `z ∈ W`. Then for every `C¹` function `φ : ℝ → ℝ`,
`∫_W w*d(φ(a) λ)⁺ ≤ liminf_k ∫_W v_k*d(φ(a) λ)⁺`, where `⁺` is the positive part of the
integrand. -/
theorem lintegral_energyDensity_le_liminf {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (W : Set ℂ) (hW : IsOpen W) (v : ℕ → ℂ → V n)
    (w : ℂ → V n) (hv : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (v k) W ∧ ∀ z ∈ W, v k z ≠ 0)
    (hw : ContDiffOn ℝ 1 w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : ∀ z ∈ W, Tendsto (fun k => v k z) atTop (𝓝 (w z)) ∧
      Tendsto (fun k => fderiv ℝ (v k) z) atTop (𝓝 (fderiv ℝ w z)))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ w z) ≤
      liminf (fun k => ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ (v k) z)) atTop := by
  sorry

end FiniteEnergyPlane
