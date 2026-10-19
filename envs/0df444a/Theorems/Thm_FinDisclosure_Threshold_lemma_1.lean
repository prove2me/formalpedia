-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_lemma_1
-- name    : FinDisclosure.Threshold.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:24.711152+00:00
-- url     : https://prove2.me/theorems/5a8930fa-4581-4789-8808-295e45d6b075
-- title:
--   Lemma 1, p. 15 — WLOG two posteriors µh, µl with E_µl c < E_µ0 c < I ≤ E_µh c, both with a pdf
-- statement:
--   Assume the standing assumptions of the model and §4's assumption $\mathbb E_{\mu_0} c(s) < I$. Let $\tau$ be any Bayes-plausible distribution over posteriors. Then there are $q \in [0,1)$ and probability measures $\mu_h, \mu_l$, both absolutely continuous with respect to Lebesgue measure (both admit a pdf), such that
--
--   1. $q\,\mu_h + (1-q)\,\mu_l = \mu_0$;
--   2. if $q > 0$ then $I \le \mathbb E_{\mu_h} c(s)$;
--   3. $\mathbb E_{\mu_l} c(s) < I$;
--   4. if $q > 0$ then $\mathbb E_{\mu_l} c(s) < \mathbb E_{\mu_0} c(s)$;
--   5. the two-point distribution $q\,\delta_{\mu_h} + (1-q)\,\delta_{\mu_l}$ is Bayes plausible and has the same value as $\tau$:
--   $$\mathbb E_{q\delta_{\mu_h} + (1-q)\delta_{\mu_l}} V(\mu) = \mathbb E_\tau V(\mu).$$
--
--   So, without loss of generality, an optimal policy puts all mass on two posteriors with $\mathbb E_{\mu_l} c < \mathbb E_{\mu_0} c < I \le \mathbb E_{\mu_h} c$. This reduction turns the problem over all distributions over posteriors into the two-posterior problem (15).
--
--   **Formalization Note** The lemma is stated for every Bayes-plausible $\tau$, not only an optimal one, so the degenerate case $q = 0$ (nothing is ever financed) is allowed; then the conditions on $\mu_h$ are vacuous. The paper's "necessarily $q \in (0,1)$" refers to the optimum. The case $q = 1$ is excluded because $\mathbb E_{\mu_0} c < I$. No hypothesis $\lambda I \le B$ is needed.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 15 (PDF 15), Lemma 1; proof p. 32 (PDF 32), §A.1

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Lemma 1, p. 15 (proof p. 32): every Bayes-plausible distribution `τ` over posteriors can be
replaced, without changing its value, by a Bayes-plausible two-point distribution putting mass `q` on a
posterior `µh` and `1 - q` on a posterior `µl`, both absolutely continuous (admitting a pdf), with
`E_{µl} c < E_{µ0} c < I ≤ E_{µh} c` (the inequalities for the posteriors that actually carry mass). -/
theorem lemma_1 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I)
    (τ : Measure (Measure ℝ)) (hτ : IsBayesPlausible (prior f0) τ) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ μh μl : Measure ℝ,
      IsProbabilityMeasure μh ∧ IsProbabilityMeasure μl ∧ μh ≪ volume ∧ μl ≪ volume ∧
      ENNReal.ofReal q • μh + ENNReal.ofReal (1 - q) • μl = prior f0 ∧
      (0 < q → I ≤ price c μh) ∧ price c μl < I ∧
      (0 < q → price c μl < price c (prior f0)) ∧
      IsBayesPlausible (prior f0)
        (ENNReal.ofReal q • Measure.dirac μh + ENNReal.ofReal (1 - q) • Measure.dirac μl) ∧
      value c I B lam
          (ENNReal.ofReal q • Measure.dirac μh + ENNReal.ofReal (1 - q) • Measure.dirac μl) =
        value c I B lam τ := by sorry

end FinDisclosure.Threshold
