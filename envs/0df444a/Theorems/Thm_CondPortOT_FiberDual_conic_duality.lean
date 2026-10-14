-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_conic_duality
-- name    : CondPortOT.FiberDual.conic_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:23.101485+00:00
-- url     : https://prove2.me/theorems/f9640aa9-9874-4f6b-acad-90eb06ea6335
-- title:
--   Proof of Theorem 4.4, p. 50 — per-sample conic duality: sup over μ₀ⁱ with E[υᵢ𝔻_𝒴] ≤ θᵢ equals inf over λᵢ ≥ 0
-- statement:
--   Let $\mathcal Y$ be a Polish space and $\mathbb D_{\mathcal Y}$ a nonnegative continuous cost on $\mathcal Y\times\mathcal Y$ with $\mathbb D_{\mathcal Y}(y,y)=0$. Fix $\hat y\in\mathcal Y$, a measurable loss $\ell:\mathcal Y\to\mathbb R$, $\upsilon\ge0$ and $\theta>0$. Then
--   $$\sup_{\substack{\mu_0\in\mathcal M(\mathcal Y)\\ \mathbb E_{\mu_0}[\upsilon\,\mathbb D_{\mathcal Y}(Y,\hat y)]\le\theta}}\mathbb E_{\mu_0}[\upsilon\,\ell(Y)]=\inf_{\lambda\ge0}\ \theta\lambda+\upsilon\sup_{y\in\mathcal Y}\big\{\ell(y)-\lambda\,\mathbb D_{\mathcal Y}(y,\hat y)\big\}.$$
--
--   The page states the summed form over $i\in[N]$; the inner problems are separable in $i$, so the summed identity is the sum of this one-sample identity. It is the step that removes the measures $\mu_0^i$ from the reformulated worst case and introduces the multipliers $\lambda_i$ of Theorem 4.4.
--
--   **Formalization Note.** Both sides are extended reals; expectations are $\int\ell^+-\int\ell^-$ and $0\cdot(\pm\infty)=0$. The restriction $\theta>0$ is added: at $\theta=0$ with $\upsilon>0$ the left side is forced to $\mu_0=\delta_{\hat y}$, while the right side is the upper envelope of $\ell$ at $\hat y$, and the two differ for a loss that is not upper semicontinuous.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 50, proof of Theorem 4.4 ("standard conic duality results [16, Theorem 1]")

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem conic_duality {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (DY : Y → Y → ℝ) (hDYnn : ∀ y y', 0 ≤ DY y y')
    (hDYc : Continuous (fun p : Y × Y => DY p.1 p.2)) (hDY0 : ∀ y, DY y y = 0)
    (yhat : Y) (L : Y → ℝ) (hL : Measurable L) (υ θ : ℝ) (hυ : 0 ≤ υ) (hθ : 0 < θ) :
    (⨆ (μ : Measure Y) (_ : IsProbabilityMeasure μ ∧
        ENNReal.ofReal υ * ∫⁻ y, ENNReal.ofReal (DY y yhat) ∂μ ≤ ENNReal.ofReal θ),
      ((υ : ℝ) : EReal) * extIntegral μ (fun y => (L y : EReal))) =
    ⨅ (l : ℝ) (_ : 0 ≤ l),
      ((θ * l : ℝ) : EReal) + ((υ : ℝ) : EReal) * ⨆ y, ((L y - l * DY y yhat : ℝ) : EReal) := by sorry

end CondPortOT.FiberDual
