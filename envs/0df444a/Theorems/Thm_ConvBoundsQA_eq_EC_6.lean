-- Prove2me | Theorems.Thm_ConvBoundsQA_eq_EC_6
-- name    : ConvBoundsQA.eq_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:09.643119+00:00
-- url     : https://prove2.me/theorems/7f340270-186c-4398-8cae-c53a98c60f94
-- title:
--   Display (EC.6) — worst-case right quantile via the reflected marginals
-- statement:
--   Let $\mu=(\mu_1,\dots,\mu_n)$ be Borel probability measures on $\mathbb R$ and $t\in[0,1)$. Let $\tilde\mu_i$ be the law of $-X_i$ for $X_i\sim\mu_i$ and $\tilde\mu=(\tilde\mu_1,\dots,\tilde\mu_n)$. Then
--   $$
--   \sup_{\nu\in\Lambda(\mu)}q^+_t(\nu)=-\inf_{\tilde\nu\in\Lambda(\tilde\mu)}q^-_{1-t}(\tilde\nu).
--   $$
--
--   Reflection turns the worst-case right quantile into a best-case left quantile, which is how the increasing-density case of Theorem 2 is reduced to known results for decreasing densities.
--
--   **Formalization Note** $\tilde\mu_i$ is the image of $\mu_i$ under $x\mapsto-x$; the supremum, infimum and negation are in `EReal`.
--
--   Differences from the source:
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
--   - generalization: the identity as written inside the proof of Theorem 2(iii), where each $\mu_i$ admits an increasing density beyond its $t$-quantile → the identity for all marginals and $t\in[0,1)$; reason: the display uses none of the case-(iii) hypotheses; it specializes to the page's use
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, (EC.6), p.43

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_Lam

open MeasureTheory

namespace ConvBoundsQA

/-- Display (EC.6): for `μ ∈ Mⁿ` and `t ∈ [0, 1)`,
`sup_{ν ∈ Λ(μ)} q⁺_t(ν) = − inf_{ν̃ ∈ Λ(μ̃)} q⁻_{1−t}(ν̃)`, where `μ̃ᵢ` is the law of `−Xᵢ` for
`Xᵢ ∼ μᵢ` (Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*,
arXiv:2007.09320v5, (EC.6), p.43).

**Formalization Note** `μ̃ᵢ` is the image of `μᵢ` under `x ↦ −x`. The supremum, infimum and negation
are taken in `EReal`. The page states (EC.6) inside the proof of Theorem 2(iii); it uses no
hypothesis of that case and is stated here for all `μ` and `t ∈ [0, 1)`. -/
theorem eq_EC_6 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (⨆ ν ∈ Lam μ, qPlus t ν) = -(⨅ ν ∈ Lam (fun i => (μ i).map (fun x => -x)), qMinus (1 - t) ν) := by sorry

end ConvBoundsQA
