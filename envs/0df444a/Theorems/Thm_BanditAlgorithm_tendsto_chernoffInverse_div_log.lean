-- Prove2me | Theorems.Thm_BanditAlgorithm_tendsto_chernoffInverse_div_log
-- name    : BanditAlgorithm.tendsto_chernoffInverse_div_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:03:29.573372+00:00
-- url     : https://prove2.me/theorems/56b71e8e-9db2-492a-94f1-ef7ade6190ab
-- title:
--   The Chernoff inverse is asymptotically log(1/δ)
-- statement:
--   The threshold constant of Lattimore--Szepesv\'ari Lemma 33.7 is asymptotically $\log(1/\delta)$: for every $k\ge1$,
--   $$\lim_{\delta\to0^+}\ \frac{f^{-1}(\delta)}{\log(1/\delta)}=1,\qquad f(x)=e^{k-x}(x/k)^k.$$
--
--   This is the exact asymptotics that make the constant in Theorem 33.6 come out to $c^*(\nu)$ and not a multiple of it: the sample complexity of Chernoff's rule is $\beta_{\tau}(\delta)/\text{(rate)}$, so any slack in $f^{-1}(\delta)/\log(1/\delta)$ would propagate directly into the limit. The lower bound is $f(x)\le\delta$ forcing $x\ge\log(1/\delta)+k+k\log(x/k)$; the upper bound is the explicit estimate $f^{-1}(\delta)\le(k+\log(1/\delta))/(1-e^{-1})$ fed back into that inequality, so the logarithmic correction is $o(\log(1/\delta))$.
-- source:
--   Exact asymptotics f^{-1}(delta) = (1+o(1)) log(1/delta) for the threshold constant of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. This is what makes the constant in Theorem 33.6 come out to c*(nu) exactly.

import Definitions.Def_TrackAndStop

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

theorem BanditAlgorithm.tendsto_chernoffInverse_div_log {k : ℕ} (hk : 0 < k) :
    Filter.Tendsto (fun δ : ℝ ↦ BanditAlgorithm.chernoffInverse k δ / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  sorry
