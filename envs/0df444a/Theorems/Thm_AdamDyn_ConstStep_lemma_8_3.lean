-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_lemma_8_3
-- name    : AdamDyn.ConstStep.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:50.406606+00:00
-- url     : https://prove2.me/theorems/ac6d67ef-a57d-49ce-b0b8-a8053b12a228
-- title:
--   Lemma 8.3 — tightness of $(\mathsf z^{\gamma,R})_{\gamma\in(0,\bar\gamma_0]}$ and $\max_{n\le\lfloor T/\gamma\rfloor}\gamma\|\sum_{k\le n}\Delta^{\gamma,R}_{k+1}\|\to0$ in probability
-- statement:
--   Assume Assumptions 2.2, 2.5, 4.1 and Assumption 4.2 ii) with $p=2$, let $\varepsilon>0$ and fix $x_0\in\mathbb R^d$. Then there is $\bar\gamma_0>0$ such that for every $R>0$:
--
--   1. the family $(\mathsf z^{\gamma,R} : \gamma\in(0,\bar\gamma_0])$ of interpolated truncated Adam processes is tight in $C([0,+\infty),\mathcal Z)$;
--   2. for every $T>0$ and every $\delta>0$,
--
--   $$
--   \mathbb P\Big(\max_{0\le n\le\lfloor T/\gamma\rfloor}\gamma\,\Big\|\sum_{k=0}^{n}\Delta^{\gamma,R}_{k+1}\Big\| > \delta\Big) \xrightarrow[\gamma\to0]{} 0 ,
--   $$
--
--   where $\Delta^{\gamma,R}_{k+1}$ is the martingale increment of the truncated iterates with respect to $\mathcal F_k=\sigma(\xi_1,\dots,\xi_k)$.
--
--   Together these give relative compactness of the interpolated processes and the vanishing of the accumulated noise, the two inputs of the ODE method.
--
--   **Formalization Note** The horizon $T$ in the second part is not quantified on the page; it is read as "for every $T>0$". Tightness follows the paper's definition (p. 7) with the compact-open topology on $C([0,+\infty),\mathcal Z)$. "Assumption 4.2" is read as 4.2 ii) with $p=2$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 22, Lemma 8.3

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Lemma 8.3 (p. 22): there is `γ̄0 > 0` such that for every `R > 0` the family of
interpolated truncated processes `(𝗓^{γ,R} : γ ∈ (0, γ̄0])` is tight in `C([0, +∞), 𝒵)`, and
for every `T > 0` and `δ > 0`,
`P(max_{0 ≤ n ≤ ⌊T/γ⌋} γ ‖Σ_{k=0}^{n} Δ^{γ,R}_{k+1}‖ > δ) → 0` as `γ → 0`.
Assumption 4.2 is read as 4.2 ii) with `p = 2`. -/
theorem lemma_8_3 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) (ξ : ℕ → Ω → Ξ)
    (αbar βbar : ℝ → ℝ) (a b ε : ℝ) (x0 : E d)
    (h22 : Assumption22 μ f gf)
    (h25 : Assumption25 αbar βbar a b)
    (h42 : Assumption42ii μ gf 2)
    (h41 : Assumption41 P μ ξ)
    (hε : 0 < ε) :
    ∃ γ0 : ℝ, 0 < γ0 ∧ ∀ R : ℝ, 0 < R →
      IsTight P (fun (γ : Set.Ioc (0 : ℝ) γ0) (ω : Ω) =>
          interp (γ : ℝ) (truncIter gf αbar βbar ε (γ : ℝ) R x0 (fun n => ξ n ω))) ∧
      ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
        Tendsto (fun γ : ℝ => P {ω | ∃ n : ℕ, n ≤ ⌊T / γ⌋₊ ∧
            δ < γ * zNorm (∑ k ∈ Finset.range (n + 1),
              noise P ξ gf αbar βbar ε γ R x0 k ω)})
          (𝓝[>] 0) (𝓝 0) := by sorry

end AdamDyn.ConstStep
