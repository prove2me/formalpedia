-- Prove2me | Theorems.Thm_DSReg_quantitative_activity
-- name    : DSReg.quantitative_activity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:31:23.610915+00:00
-- url     : https://prove2.me/theorems/62c9e2ac-2a77-4aff-83cd-d20a72d3505e
-- title:
--   Lemma 5: quantitative activity
-- statement:
--   Let $x=g(z)$, with $g$ differentiable $\mu$-a.e. and measurable Jacobian $D$. Assume Functional no-cancellation and the bounded-rows condition $\|D_{r,:}(z)\|_2\le M$ for all rows $r$ and $\mu$-a.e. $z$. Let $r$ be a row with $I_r\ne\emptyset$, let $c\in\mathbb{R}^{I_r}$ with $\|c\|_2\le1$, and set $f_c=\sum_{i\in I_r}c_iD_{ri}$. Then for every $0\le t<\sigma_r\|c\|_2$,
--
--   $$\mu\big(|f_c|>t\big)\ge\frac{\sigma_r^2\|c\|_2^2-t^2}{M^2}>0.$$
--
--   **Formalization Note** $c$ is a vector on $[d]$ that vanishes off $I_r$. The bounded-rows condition $\operatorname{ess\,sup}_z\max_r\|D_{r,:}(z)\|_2\le M$ is written as an almost-everywhere bound.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.4, Lemma 5, p. 22

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem quantitative_activity {d p : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin d → ℝ) → Fin p → ℝ) (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z)
    (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (hfnc : FunctionalNoCancellation μ (depJac g))
    (M : ℝ) (hM : ∀ᵐ z ∂μ, ∀ r, vecNorm (fun i => depJac g z r i) ≤ M)
    (r : Fin p) (hr : (activeRow μ (depJac g) r).Nonempty)
    (c : Fin d → ℝ) (hc : ∀ i, i ∉ activeRow μ (depJac g) r → c i = 0) (hc1 : vecNorm c ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < sigmaRow μ (depJac g) r * vecNorm c) :
    (sigmaRow μ (depJac g) r ^ 2 * vecNorm c ^ 2 - t ^ 2) / M ^ 2 ≤
        (μ {z | t < |∑ i, c i * depJac g z r i|}).toReal ∧
      0 < (sigmaRow μ (depJac g) r ^ 2 * vecNorm c ^ 2 - t ^ 2) / M ^ 2 := by sorry

end DSReg
