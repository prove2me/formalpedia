-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoffInverse_ge_sharp_lower_bound
-- name    : BanditAlgorithm.chernoffInverse_ge_sharp_lower_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T22:02:02.419298+00:00
-- url     : https://prove2.me/theorems/c0670c83-18f9-4396-a959-070a8547f8b4
-- title:
--   Sharp lower bound on the threshold constant of Chernoff's stopping rule
-- statement:
--   Taking logarithms in `f(f^{-1}(δ)) ≤ δ`, where $f(x)=e^{k-x}(x/k)^k$, gives the sharp lower bound
--   $$f^{-1}(\delta)\ \ge\ k+\log\frac1\delta+k\log\frac{f^{-1}(\delta)}{k}.$$
--
--   Dropping the last term (it is nonnegative, since $f^{-1}(\delta)\ge k$) recovers the crude $f^{-1}(\delta)\ge k+\log(1/\delta)$. The last term is what one cannot afford to drop: it grows like $k\log\log(1/\delta)$, and it is exactly the slack that pays for the $\tfrac12\log(1+cT_i)$ prices incurred by a self-normalised mixture martingale run at prior variance $c\approx f^{-1}(\delta)$. Without it the mixture argument fails for small $\delta$ no matter how the variance is tuned.
-- source:
--   Elementary consequence of the defining property of f^{-1} for the function f(x) = e^{k-x}(x/k)^k of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. The sharp form (with the logarithmic correction retained) is what the mixture-martingale proof of the pairwise deviation bound needs.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

theorem BanditAlgorithm.chernoffInverse_ge_sharp_lower_bound {k : ℕ} (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) + Real.log (1 / δ)
        + (k : ℝ) * Real.log (BanditAlgorithm.chernoffInverse k δ / (k : ℝ))
      ≤ BanditAlgorithm.chernoffInverse k δ := by
  sorry
