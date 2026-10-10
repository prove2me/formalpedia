-- Prove2me | Theorems.Thm_BenfordLaw_exponential_growth_benford
-- name    : BenfordLaw.exponential_growth_benford
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:58.147342+00:00
-- url     : https://prove2.me/theorems/7e8f31d0-0ab6-4c9b-ad4a-0e4868445b02
-- title:
--   Exponential growth or decay obeys Benford's law in time average
-- statement:
--   Let $Q(t) = C e^{rt}$ with $C > 0$ and growth rate $r \neq 0$ (growth if $r>0$, decay if $r<0$). For every digit $d\in\{1,\dots,9\}$, the fraction of the time interval $[0,T]$ during which $Q$ has leading digit $d$ tends to the Benford probability:
--   $$\lim_{T\to\infty}\frac{\lambda\big(\{t\in[0,T] : D_{10}(Q(t)) = d\}\big)}{T} = \log_{10}\!\left(1+\frac1d\right),$$
--   where $\lambda$ is Lebesgue measure on $\mathbb R$.
--
--   This is the continuous-time analogue of the sequence results.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Distributions known to obey Benford's law" ("If a quantity is exponentially increasing or decreasing in time, then the percentage of time that it has each first digit satisfies Benford's law asymptotically").

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem exponential_growth_benford (C r : ℝ) (hC : 0 < C) (hr : r ≠ 0)
    (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun T : ℝ =>
        (MeasureTheory.volume
          {t : ℝ | t ∈ Set.Icc 0 T ∧ leadingDigit 10 (C * Real.exp (r * t)) = d}).toReal / T)
      Filter.atTop (nhds (benfordProb 10 d)) := by sorry

end BenfordLaw
