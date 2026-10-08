-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_lemma_8_4
-- name    : AdamDyn.ConstStep.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:51.25672+00:00
-- url     : https://prove2.me/theorems/bea909fe-ae8f-4de6-a6c4-75bf89151747
-- title:
--   Lemma 8.4 — $h_{\gamma_n}(\varphi_n,z_n)\to h(t,z)$ and $e_{\gamma_n}(\varphi_n,z_n)\to\bar e(t,z)$ when $\gamma_n\varphi_n\to t$
-- statement:
--   Assume Assumptions 2.2 and 2.5 (with limits $a,b$), let $\varepsilon>0$, and let $F$, $S$ be given by (2.2). Let $t>0$ and $z\in\mathcal Z_+$. Let $(\gamma_n)$ be positive step sizes with $\gamma_n\to0$, $(\varphi_n)$ positive integers and $(z_n)$ points of $\mathcal Z_+$ such that
--
--   $$
--   \lim_{n\to\infty}\gamma_n\varphi_n = t \quad\text{and}\quad \lim_{n\to\infty} z_n = z .
--   $$
--
--   Then $\lim_{n\to\infty} h_{\gamma_n}(\varphi_n,z_n) = h(t,z)$ and $\lim_{n\to\infty} e_{\gamma_n}(\varphi_n,z_n) = \bar e(t,z)$, where $h_\gamma$ is the mean field (3.2), $h$ the continuous-time Adam field (3.3), $e_\gamma$ the discrete debiasing map and $\bar e$ its continuous-time counterpart.
--
--   This identifies the non-autonomous ODE as the limit of the mean dynamics of constant-step Adam at time $t\approx n\gamma$.
--
--   **Formalization Note** The sequence $(\gamma_n)$ is not introduced in the lemma; it is the step-size sequence of the regime $\gamma\to0$ in which the lemma is used (p. 23). The hypotheses $\gamma_n>0$ and $\gamma_n\to0$ are stated explicitly; without $\gamma_n\to0$ the conclusion fails (e.g. $\varphi_n=1$, $\gamma_n=t$).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 22, Lemma 8.4

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Lemma 8.4 (p. 22): if `γ_n > 0`, `γ_n → 0`, `φ_n ∈ ℕ*`, `γ_n φ_n → t > 0` and
`z_n → z` in `𝒵₊`, then `h_{γ_n}(φ_n, z_n) → h(t, z)` and `e_{γ_n}(φ_n, z_n) → ē(t, z)`,
with `F`, `S` given by (2.2). The step sizes `γ_n`, not introduced on the page, are those of
the regime of §8.1 (`γ_n → 0`). -/
theorem lemma_8_4 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ) (a b ε : ℝ)
    (h22 : Assumption22 μ f gf)
    (h25 : Assumption25 αbar βbar a b)
    (hε : 0 < ε)
    (t : ℝ) (ht : 0 < t) (z : Z d) (hz : InZplus z)
    (γs : ℕ → ℝ) (hγpos : ∀ n, 0 < γs n) (hγlim : Tendsto γs atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : ∀ n, 1 ≤ φ n)
    (zs : ℕ → Z d) (hzs : ∀ n, InZplus (zs n))
    (hγφ : Tendsto (fun n => γs n * (φ n : ℝ)) atTop (𝓝 t))
    (hzlim : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => hGamma μ gf αbar βbar ε (γs n) (φ n) (zs n)) atTop
        (𝓝 (AdamDyn.WellPosed.adamField a b ε (objective μ f) (sqGradMean μ gf) t z)) ∧
      Tendsto (fun n => eGamma αbar βbar (γs n) (φ n) (zs n)) atTop (𝓝 (AdamDyn.ODEConv.ebar a b t z)) := by sorry

end AdamDyn.ConstStep
