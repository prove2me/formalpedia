-- Prove2me | Theorems.Thm_FastCLO_ETO_peeled_bound
-- name    : FastCLO.ETO.peeled_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:25.281614+00:00
-- url     : https://prove2.me/theorems/c3ed1ad0-5844-4eb5-bf63-0bf543402f65
-- title:
--   Proof of Theorem 8, peeled bound — Regret(π_f̂) ≤ 2BδP(0 < Δ ≤ 2Bδ) + Bδ Σ_r 2^{r+1} P(‖f* − f̂‖ > 2^{r−1}δ, 0 < Δ ≤ 2^{r+1}Bδ)
-- statement:
--   Let $\mathcal Z$ be a polytope with norm bound $B$, fix an instance with feature law $\mathbb P_X$ and regression function $f^*$, and a sample size $n$. Let $\hat f$ be an estimator, mapping every data set $\mathcal D$ of size $n$ to a function $\hat f_{\mathcal D} : \mathbb R^p \to \mathbb R^d$, and let $\pi_{\hat f}$ assign to every $\mathcal D$ a plug-$\hat f_{\mathcal D}$-in policy. Assume $(\mathcal D, x) \mapsto \hat f_{\mathcal D}(x)$ and $(\mathcal D, x) \mapsto \pi_{\hat f, \mathcal D}(x)$ are jointly measurable. Then for every $\delta > 0$,
--
--   $$\mathrm{Regret}(\pi_{\hat f}) \le 2B\delta\,\mathbb P\bigl(0 < \Delta(X) \le 2B\delta\bigr) + B\delta \sum_{r=1}^\infty 2^{r+1}\,\mathbb P\bigl(\|f^*(X) - \hat f(X)\| > 2^{r-1}\delta,\ 0 < \Delta(X) \le 2^{r+1}B\delta\bigr),$$
--
--   where the probabilities in the series are over the pair $(\mathcal D, X)$, with $\mathcal D \sim \mathbb P^n$ and $X \sim \mathbb P_X$ independent.
--
--   This is the peeling step of the proof of Theorem 8: the regret is split according to the dyadic shell in which the estimation error falls, and in each shell a decision error forces a small positive gap. Neither the noise condition nor the tail condition is used yet.
--
--   **Formalization Note** The series is indexed from $0$ in Lean (the paper's $r$ is Lean's $r + 1$). The inequality is stated between extended nonnegative reals, because without a tail condition the series may diverge; the regret is nonnegative, so nothing is lost. The paper writes $\|f(X) - \hat f(X)\|$ where it means $\|f^*(X) - \hat f(X)\|$. Joint measurability is not stated in the paper; it makes the regret a genuine integral.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 8 (Appendix A.5), the peeling chain, p. 30

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FastCLO.ETO

/-- **Proof of Theorem 8, the peeled bound** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear
Optimization*, arXiv:2011.03030v3, Appendix A.5, p. 30): "fixing δ > 0 and peeling on
‖f(X) − f̂(X)‖, we obtain `Regret(π_f̂) ≤ 2BδP(0 < Δ(X) ≤ 2Bδ) + Bδ Σ_{r=1}^∞ 2^{r+1}
P(‖f*(X) − f̂(X)‖ > 2^{r−1}δ, 0 < Δ(X) ≤ 2^{r+1}Bδ)`."

Here `fhat D` is the estimate computed from the data `D`, `pihat D` a plug-in policy for it, and the
probability in the series is over the pair `(D, X)`, `D` drawn from `n` i.i.d. copies of
`(X, Y)` and `X` independent of `D`.

Formalization Note: the page's index `r ≥ 1` is re-indexed as `r + 1` with `r ≥ 0`. The bound is
stated in `ℝ≥0∞` because, without a tail condition on `f̂`, the series need not converge; the regret
is nonnegative, so `ENNReal.ofReal` loses nothing. The page's `‖f(X) − f̂(X)‖` is read as
`‖f*(X) − f̂(X)‖`. Joint measurability of `fhat` and `pihat` in `(D, x)` is assumed so that the
regret is a genuine integral (the page leaves it implicit). Neither the noise condition nor the tail
condition is used at this step. -/
theorem peeled_bound {p d : ℕ} (P : Polytope d) (I : Instance p d) (n : ℕ)
    (fhat pihat : (Fin n → FastCLO.ERM.Vec p × FastCLO.ERM.Vec d) → FastCLO.ERM.Vec p → FastCLO.ERM.Vec d)
    (hplug : ∀ D, IsPlugIn P (fhat D) (pihat D))
    (hf : Measurable (Function.uncurry fhat)) (hpi : Measurable (Function.uncurry pihat))
    (δ : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (regret P I n pihat) ≤
      ENNReal.ofReal (2 * P.B * δ) * I.μ {x | 0 < gap P I x ∧ gap P I x ≤ 2 * P.B * δ} +
      ENNReal.ofReal (P.B * δ) * ∑' r : ℕ, (2 : ℝ≥0∞) ^ (r + 2) *
        ((I.sample n).prod I.μ) {q | 2 ^ r * δ < ‖I.fstar q.2 - fhat q.1 q.2‖ ∧
          0 < gap P I q.2 ∧ gap P I q.2 ≤ 2 ^ (r + 2) * P.B * δ} := by sorry

end FastCLO.ETO
