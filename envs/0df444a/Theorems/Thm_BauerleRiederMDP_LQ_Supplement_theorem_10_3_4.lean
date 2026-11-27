-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_10_3_4
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_10_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:09:16.690637+00:00
-- url     : https://prove2.me/theorems/d2b20e4a-1876-5c85-847d-615b57d0fed2
-- title:
--   Theorem 10.3.4 (corrected: positive-part bound) — Bayesian stopping: values and thresholds increase when the density is MTP_2
-- statement:
--   If the density $q(z|\theta )$ is $MTP_2$ in $z$ and $\theta $, then the functions $(x, i) \mapsto  J_n(x, i)$ and $i \mapsto  c_n(i)$ are increasing for all $n$.
--
--   **Formalization Note.** The order on $I$ is $i \le  i' :⇔ \hat{\mu}(\cdot |i) \le _lr \hat{\mu}(\cdot |i')$ (p.324, Definition B.3.5) and on $E = \mathbb R  \times  I$ it is $(x, i) \le  (x', i') :⇔ x \le  x', i \le  i'$. $MTP_2$ of the bivariate density means $q(z|\theta ') q(z'|\theta ) \le  q(z|\theta ) q(z'|\theta ')$ for $z \le  z'$, $\theta  \le  \theta '$ in $\Theta $. The printed assumption $\sup _\theta  \int  z Q(dz|\theta ) < \infty $ made for (B_N) (p.324) is corrected to the positive part $\int  z^+ Q(dz|\theta )$, the quantity (B_N) actually bounds. $J_n$ is the $n$-stage value function ($J_0(x, i) = x$), and $c_n$ is stated for $n \ge  1$. $\hat{\mu}$ and $\hat{\Phi}$ are any measurable kernel and update with the Bayes identity of `BayesStopping.bayes`, in particular those of a sequential sufficient statistic.
--
--   Differences from the source:
--   - generalization: μ̂, Φ̂ of a sequential sufficient statistic → any measurable kernel μ̂ and update Φ̂ with the Bayes identity; reason: the sufficient-statistic objects satisfy it; the proof uses only the identity
--   - correction: sup_θ ∫ z Q(dz|θ) < ∞ → sup_θ ∫ z⁺ Q(dz|θ) < ∞; reason: (B_N) on p.304 bounds the positive part of the stopping reward; the literal signed-mean condition does not imply that bound
--   - encoding: substochastic model → absorbing stopped state with zero rewards; reason: Example 2.3.13; same values
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.3.4, p.324 (PDF 332)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_LROrder
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_mdp
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_J
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_cThr

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 10.3.4** (corrected positive-part bound) (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 10.3.4, p.324, PDF 332, Bayesian stopping problem of §10.3.4, pp.323–324,
PDF 331–332). If the density `q(z|θ)` is `MTP_2` in `z` and `θ`, then the functions
`(x, i) ↦ J_n(x, i)` and `i ↦ c_n(i)` are increasing for all `n`.

**Formalization Note.** The order on `I` is `i ≤ i′ :⇔ μ̂(·|i) ≤_lr μ̂(·|i′)` (p.324,
Definition B.3.5) and on `E = ℝ × I` it is `(x, i) ≤ (x′, i′) :⇔ x ≤ x′, i ≤ i′`. `MTP_2` of the
bivariate density means `q(z|θ′) q(z′|θ) ≤ q(z|θ) q(z′|θ′)` for `z ≤ z′`, `θ ≤ θ′` in `Θ`. The
printed assumption `sup_θ ∫ z Q(dz|θ) < ∞` made for (B_N) (p.324) is corrected to the positive part
`∫ z⁺ Q(dz|θ)`, the quantity (B_N) actually bounds. `J_n` is the `n`-stage value function (`J_0(x, i) = x`), and
`c_n` is stated for `n ≥ 1`. `μ̂` and `Φ̂` are any measurable kernel and update with the Bayes
identity of `BayesStopping.bayes`, in particular those of a sequential sufficient statistic. -/
theorem theorem_10_3_4 {SΘ : Set ℝ} {I : Type} [MeasurableSpace I] (P : BayesStopping SΘ I)
    (hbound : ∃ C : ℝ, ∀ θ, ∫⁻ z, ENNReal.ofReal z ∂(P.Qk θ) ≤ ENNReal.ofReal C)
    (hMTP2 : ∀ (z z' : ℝ) (θ θ' : SΘ), z ≤ z' → θ ≤ θ' → P.q z θ' * P.q z' θ ≤ P.q z θ * P.q z' θ') :
    (∀ (n : ℕ) (x x' : ℝ) (i i' : I), x ≤ x' → LROrder (P.muhat i) (P.muhat i') →
        P.J n x i ≤ P.J n x' i') ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i i' : I, LROrder (P.muhat i) (P.muhat i') → P.cThr n i ≤ P.cThr n i' := by sorry

end BauerleRiederMDP.LQ.Supplement
