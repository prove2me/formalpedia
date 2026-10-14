-- Prove2me | Theorems.Thm_Apery_theta_eventually_close
-- name    : Apery.theta_eventually_close
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:19:48.551982+00:00
-- url     : https://prove2.me/theorems/dc339b40-f1b6-4f4a-8006-d2145108d771
-- title:
--   The prime number theorem in $\varepsilon$-form: $\theta(y) \sim y$
-- statement:
--   For every $\varepsilon > 0$, for all sufficiently large real $y$,
--
--   $$\bigl|\theta(y) - y\bigr| \;\le\; \varepsilon\, y,$$
--
--   where $\theta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. This is the $\varepsilon$-form of the prime number theorem in the form $\theta(y) \sim y$; it is the external analytic input of the small-prime range of the normaliser's growth estimate (source `Apery/Growth.lean` uses it through `Apery/PrimeSum.lean`, lemma `theta_eventually_close`, which imports the prime number theorem ($\theta(x) \sim x$) from the external project `PrimeNumberTheoremAnd`; Mathlib does not contain it). **Formalization Note** The statement is the source's. On the platform the closest available results are Mathlib's upper bound $\theta(x) \le (\log 4)x$ and the proved lower bound `FamousTheorems.chebyshev_theta_lower_bound`; the open platform targets `IntMul.HvdH.rosser_schoenfeld_thm4` and `TaoFivePrimes.dusart_theta_error_log_four_chebyshev` are strong explicit forms that imply this statement.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/PrimeSum.lean#L41-L48 (from Apery/PNT.lean)

import Mathlib

open Filter

namespace Apery

lemma theta_eventually_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y - y| ≤ ε * y := by
  sorry

end Apery
