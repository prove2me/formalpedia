-- Prove2me | Theorems.Thm_ForecastAggLearn_logit_space_loss
-- name    : ForecastAggLearn.logit_space_loss
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:25.143441+00:00
-- url     : https://prove2.me/theorems/2224e15d-b40f-4e88-b565-0cc8aacbc480
-- title:
--   §4.1 — the expected log loss in log-likelihood space, $\tilde L(\tilde r)=-(r^*-1)\tilde r+\ln(1+e^{-\tilde r})$
-- statement:
--   Let $q=r^*(s)\in[0,1]$ and let the aggregator report a log-likelihood $\tilde r\in\mathbb R$, i.e. the forecast $r=(1+\exp(-\tilde r))^{-1}$. Then its expected logarithmic loss is
--
--   $$
--   \begin{aligned}
--   \tilde L(\tilde r)&=-q\ln\Bigl(\frac{1}{1+\exp(-\tilde r)}\Bigr)-(1-q)\ln\Bigl(\frac{\exp(-\tilde r)}{1+\exp(-\tilde r)}\Bigr)\\
--   &=-q\tilde r-\ln\Bigl(\frac{\exp(-\tilde r)}{1+\exp(-\tilde r)}\Bigr)\\
--   &=-(q-1)\tilde r+\ln\bigl(1+\exp(-\tilde r)\bigr),
--   \end{aligned}
--   $$
--
--   and $\tilde L(\tilde r)=q\,l(r,1)+(1-q)\,l(r,0)$.
--
--   In log-likelihood space the log loss becomes a logistic loss, which is convex in the report; this is the loss online gradient descent is run on.
--
--   **Formalization Note** The last identity is stated in $[0,\infty]$ with the loss `logLoss`.
--
--   Differences from the source:
--   - encoding: r*(s) in the display; "the aggregator's logarithmic loss is given by L̃(r̃)" → q ∈ [0, 1] in place of r*(s); the identity with the expected loss q·l(r,1) + (1 − q)·l(r,0) of r = (1 + e^{−r̃})^{−1} stated in ℝ≥0∞; reason: r*(s) ranges over [0, 1]; the last clause is the sentence introducing the display
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.1, display, p.16

import Mathlib
import Definitions.Def_ForecastAggLearn_logLoss

namespace ForecastAggLearn

/-- **The expected log loss in log-likelihood space.**
Babichenko, Garber, arXiv:1802.07107v1, §4.1, display, p.16: for a forecast given in
log-likelihood form `r̃` (the forecast is `(1 + exp(−r̃))^{−1}`),

`L̃(r̃) = −r* ln(1/(1 + exp(−r̃))) − (1 − r*) ln(exp(−r̃)/(1 + exp(−r̃)))
      = −r* r̃ − ln(exp(−r̃)/(1 + exp(−r̃)))
      = −(r* − 1) r̃ + ln(1 + exp(−r̃))`.

The three real expressions are equal for every `q = r* ∈ [0, 1]` and `r̃ ∈ ℝ`, and they equal the
expected log loss `q l(r, 1) + (1 − q) l(r, 0)` of the forecast `r = (1 + exp(−r̃))^{−1}`.

**Formalization Note.** The last clause links the display to `logLoss` (in `ℝ≥0∞`). -/
theorem logit_space_loss (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (rt : ℝ) :
    -q * Real.log (1 / (1 + Real.exp (-rt))) -
          (1 - q) * Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) =
        -q * rt - Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) ∧
      -q * rt - Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) =
        -(q - 1) * rt + Real.log (1 + Real.exp (-rt)) ∧
      ENNReal.ofReal q * logLoss (1 / (1 + Real.exp (-rt))) true +
          ENNReal.ofReal (1 - q) * logLoss (1 / (1 + Real.exp (-rt))) false =
        ENNReal.ofReal (-(q - 1) * rt + Real.log (1 + Real.exp (-rt))) := by sorry

end ForecastAggLearn
