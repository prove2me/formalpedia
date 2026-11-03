-- Prove2me | Theorems.Thm_DNNProj_proposition_8
-- name    : DNNProj.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:14.76388+00:00
-- url     : https://prove2.me/theorems/10922551-ffcc-4ff5-87d4-1e6e52e865a5
-- title:
--   Proposition 8 — $\partial\delta_{\mathbb S^n_+}$ is metrically subregular at $\bar X$ for $-\bar S$, and $\partial\delta_{\mathbb S^n_-}$ at $-\bar S$ for $\bar X$
-- statement:
--   Let $\bar S\in\mathbb S^n_+$ and $0\in\bar X+\partial\delta_{\mathbb S^n_+}(\bar S)$. Then
--
--   1. $\partial\delta_{\mathbb S^n_+}(\cdot)$ is metrically subregular at $\bar X$ for $-\bar S$, and
--   2. $\partial\delta_{\mathbb S^n_-}(\cdot)$ is metrically subregular at $-\bar S$ for $\bar X$,
--
--   both as set-valued maps $\mathbb S^n\rightrightarrows\mathbb S^n$, where $\mathbb S^n_-=-\mathbb S^n_+$. With Proposition 3 this gives the quadratic growth of $\delta_{\mathbb S^n_+}$ needed for Assumption 1(b) of (D). The paper's proof produces the modulus $\kappa=\bar\lambda_{|\alpha|}/(2|\bar\lambda_n|+3\rho+2|\beta|\rho)$ with $\rho=\min\{|\bar\lambda_j|:j\in\gamma\}$.
--
--   **Formalization Note** $\partial\delta_C$ is the subdifferential of the `EReal` indicator of $C$. Metric subregularity is Definition 2 for some modulus.
--
--   Differences from the source:
--   - encoding: Sⁿ with the Frobenius inner product → SunNLSDP.Equiv.SymMat (Fin n); reason: its inherited inner product is the Frobenius product
--   - encoding: functions with values in (−∞, +∞] → EReal-valued functions; θ(x̄), p(x) at points where they are finite enter as real numbers (toReal); reason: Lean convention; the values are finite at every such point (the subdifferential there is nonempty), so no instance changes
--   - encoding: ∂f(x), the convex-analysis subdifferential → subdiff f x, empty where f x is not finite; reason: standard convention for proper functions; ∂f(x) = ∅ off dom f
--   - encoding: Definition 2 with dist(ȳ, F(x)), possibly over F(x) = ∅ → Metric.infEDist (values in [0, ∞]) on both sides, with modulus κ > 0 existentially quantified; reason: dist to the empty set is +∞ as the infimum over ∅; Metric.infDist would give 0 and change the property
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 8, p.11 (proof pp.11–13)

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_DNN

open scoped RealInnerProductSpace

namespace DNNProj

/-- **Proposition 8** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.11). Let `S̄ ∈ Sⁿ₊` and
`0 ∈ X̄ + ∂δ_{Sⁿ₊}(S̄)`. Then `∂δ_{Sⁿ₊}(·)` is metrically subregular at `X̄` for `−S̄`, and
`∂δ_{Sⁿ₋}(·)` is metrically subregular at `−S̄` for `X̄`.

**Formalization Note.** Both maps are `Sⁿ ⇒ Sⁿ` (symmetric matrices, Frobenius norm);
`Sⁿ₋ = −Sⁿ₊`. `∂δ_C` is the subdifferential of the `EReal` indicator. Metric subregularity is
Definition 2 for some modulus `κ > 0` (`MetricSubregular`, with `infEDist`). The modulus built in
the paper's proof (p.13) is `κ = λ̄_{|α|}/(2|λ̄ₙ| + 3ρ + 2|β|ρ)` with `ρ = min{|λ̄ⱼ| : j ∈ γ}`;
the statement, like the page, asserts only existence. -/
theorem proposition_8 {n : ℕ} (Sbar Xbar : Sym n) (hS : Sbar ∈ psd n)
    (h0 : -Xbar ∈ subdiff (indicatorE (psd n)) Sbar) :
    MetricSubregular (subdiff (indicatorE (psd n))) Xbar (-Sbar) ∧
      MetricSubregular (subdiff (indicatorE (nsd n))) (-Sbar) Xbar := by sorry

end DNNProj
