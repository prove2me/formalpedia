-- Prove2me | Theorems.Thm_ForecastAggLearn_logLoss_proper
-- name    : ForecastAggLearn.logLoss_proper
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:11.704519+00:00
-- url     : https://prove2.me/theorems/27175da9-f016-4f1b-a2a0-17457719a88b
-- title:
--   §2 — logarithmic loss is a proper scoring rule
-- statement:
--   Let $q\in[0,1]$ play the role of the Bayes posterior $r^*(s)$, and for a forecast $r\in[0,1]$ let
--
--   $$
--   L(r)=q\,l(r,1)+(1-q)\,l(r,0)=-q\ln r-(1-q)\ln(1-r)
--   $$
--
--   be the expected logarithmic loss. Then $L$ is minimized at $r=q$:
--
--   $$
--   L(q)\le L(r)\qquad\text{for every } r\in[0,1].
--   $$
--
--   This is why the benchmark of the paper is $r^*(s)$: with the signals in hand no forecast has smaller expected loss, and the regret of any aggregator is nonnegative in expectation given $s$.
--
--   **Formalization Note** Losses take values in $[0,\infty]$ with $-\ln 0=\infty$ and $0\cdot\infty=0$.
--
--   Differences from the source:
--   - encoding: expected loss L(r) = −r*(s) ln r − (1 − r*(s)) ln(1 − r) in ℝ → q · l(r, 1) + (1 − q) · l(r, 0) in ℝ≥0∞ with l = logLoss and q ∈ [0, 1] in place of r*(s); reason: Lean convention for ln 0 = −∞; r*(s) ranges over [0, 1]
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.10

import Mathlib
import Definitions.Def_ForecastAggLearn_logLoss

namespace ForecastAggLearn

/-- **Logarithmic loss is a proper scoring rule.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.10: "The aggregator's objective is to minimize his
expected logarithmic loss, which is given by L(y) = −r*(s) ln(r) − (1 − r*(s)) ln(1 − r). The
expected loss L(y) is minimized at r = r*(s), because logarithmic loss is a proper scoring rule."

For every `q ∈ [0, 1]` (the role of `r*(s)`) and every forecast `r ∈ [0, 1]`, the expected log
loss `q l(r, 1) + (1 − q) l(r, 0)` is at least its value at `r = q`.

**Formalization Note.** The expected loss is computed in `ℝ≥0∞`, with `l(0, 1) = l(1, 0) = +∞`
and `0 · ∞ = 0`. -/
theorem logLoss_proper (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal q * logLoss q true + ENNReal.ofReal (1 - q) * logLoss q false ≤
      ENNReal.ofReal q * logLoss r true + ENNReal.ofReal (1 - q) * logLoss r false := by sorry

end ForecastAggLearn
