-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_doob_endpoint_conditioned_bridge_kernel_normalised
-- name    : AppliedSDE.SarkkaSolin.doob_endpoint_conditioned_bridge_kernel_normalised
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:56:31.304549+00:00
-- url     : https://prove2.me/theorems/0a7e7585-fb1b-4d1e-b394-d42e933b325a
-- title:
--   General Doob endpoint-conditioned transition kernel integrates to one
-- statement:
--   Original derived from Theorem 7.11, equations (7.73)–(7.79), printed pp. 113–115. Let p(s,x;t,y) be a nonnegative scalar diffusion transition density with Chapman–Kolmogorov consistency. For s<t<T and a terminal endpoint z with positive transition density p(s,x;T,z), the Doob h-transform transition density is p(s,x;t,y) p(t,y;T,z) / p(s,x;T,z). Its integral in the intermediate state is one. This captures the general conditioned bridge kernel normalisation; the full conditioned process law and SDE drift theorem remain distinct obligations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   p^h(s,x;t,y)=\frac{p(s,x;t,y)p(t,y;T,z)}{p(s,x;T,z)}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.11, equations (7.79)–(7.82), Doob bridge kernel, printed p. 115. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.doob_endpoint_conditioned_bridge_kernel_normalised
    (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (s x t T z : ℝ) (hst : s < t) (htT : t < T)
    (hpositive : 0 < p s x T z)
    (hIntegrable : Integrable
      (fun y : ℝ => p s x t y * p t y T z))
    (hCK : ∫ y : ℝ, p s x t y * p t y T z =
      p s x T z) :
    ∫ y : ℝ, p s x t y * p t y T z / p s x T z = 1 := by
  sorry
