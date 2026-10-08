-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_prophet_tendsto
-- name    : CorreaThreshold.Tight.prophet_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:31.175336+00:00
-- url     : https://prove2.me/theorems/50d4a7c2-5b87-42ab-ae39-dd7f99970411
-- title:
--   §3.1 — the prophet value tends to (e − 1)/(e − 2)
-- statement:
--   Let $P_n$ be the expected maximum of $n^2$ independent rewards from the three point law $\mu_n$ of Section 3.1. Then
--
--   $$
--   P_n\longrightarrow\frac{e-1}{e-2}\qquad(n\to\infty).
--   $$
--
--   This identifies the benchmark used to turn the rule's limiting reward into an approximation factor.
--
--   **Formalization Note** The limit is stated in $[0,\infty]$. The definition assigns a dummy value at $n=0$ to make $P_n$ total; this has no effect on the limit.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1461, §3.1; p. 1474, Appendix B

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem prophet_tendsto :
    Filter.Tendsto prophet Filter.atTop
      (nhds (ENNReal.ofReal ((Real.exp 1 - 1) / (Real.exp 1 - 2)))) := by sorry

end CorreaThreshold.Tight
