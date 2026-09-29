-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoffInverse_le_one_add_eps_mul_log
-- name    : BanditAlgorithm.chernoffInverse_le_one_add_eps_mul_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:24:29.923282+00:00
-- url     : https://prove2.me/theorems/43355cec-f2dc-433c-b87a-81106b568164
-- title:
--   Lemma 33.7: $f^{-1}(\delta)\le(1+\varepsilon)\big(k\log\tfrac1\delta+\ldots\big)$
-- statement:
--   Let $f(x)=e^{k-x}(x/k)^k$ and let $f^{-1}(\delta)$ be the least $x\ge k$ with $f(x)\le\delta$, as in Lattimore--Szepesv\'ari Lemma 33.7. For every $\varepsilon>0$ and every $\delta\in(0,1]$,
--   $$f^{-1}(\delta)\ \le\ (1+\varepsilon)\log\frac1\delta\ +\ k+k(1+\varepsilon)\log\frac{1+\varepsilon}{\varepsilon}.$$
--
--   Two bounds on $f^{-1}$ are already easy: the order bound $f^{-1}(\delta)\le (k+\log(1/\delta))/(1-e^{-1})$, whose multiplicative constant $1.582\dots$ is too lossy to keep the leading constant of Theorem 33.6 exact, and the asymptotic $f^{-1}(\delta)/\log(1/\delta)\to1$, which has the right constant but only holds eventually in $\delta$. The sample-complexity argument needs both at once, and that is what this is: multiplicative constant $1+\varepsilon$, valid at *every* confidence level, the excess absorbed into an additive constant depending only on $k$ and $\varepsilon$.
--
--   The mechanism is the choice of tangent. The order bound estimates $\log y\le y/e$, the tangent to the logarithm at $y=e$; replacing it by the tangent at an arbitrary point $c$, $\log y\le y/c+\log c-1$, makes the linear coefficient $1/c$ as small as desired at the cost of an additive $k\log c$. Taking $c=(1+\varepsilon)/\varepsilon$ makes the coefficient of $\log(1/\delta)$ come out to exactly $1+\varepsilon$.
--
--   The blow-up of the additive constant as $\varepsilon\to0$ is not an artefact: $f^{-1}(\delta)-\log(1/\delta)\sim k\log\log(1/\delta)$ is unbounded, so no bound with $\varepsilon=0$ and a constant can hold.
-- source:
--   Quantitative form of the threshold constant of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410, in the form needed for the leading constant of their Theorem 33.6; cf. Garivier & Kaufmann, COLT 2016, Section 5.

import Definitions.Def_TrackAndStop

open Real

theorem BanditAlgorithm.chernoffInverse_le_one_add_eps_mul_log {k : ℕ} (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    BanditAlgorithm.chernoffInverse k δ
      ≤ (1 + ε) * Real.log (1 / δ)
        + ((k : ℝ) + (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε)) := by
  sorry
