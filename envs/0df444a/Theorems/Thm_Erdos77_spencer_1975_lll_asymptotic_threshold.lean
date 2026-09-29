-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_lll_asymptotic_threshold
-- name    : Erdos77.spencer_1975_lll_asymptotic_threshold
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:27:37.978987+00:00
-- url     : https://prove2.me/theorems/c85d336d-94cd-4d63-892f-6f6985974bee
-- title:
--   Spencer 1975 - asymptotic local lemma threshold
-- statement:
--   Fix a real number epsilon with 0 < epsilon < 1, and put
--
--   $$n_k=\left\lfloor(1-\varepsilon)\frac{\sqrt{2}}{e}k2^{k/2}\right\rfloor.$$
--
--   For all sufficiently large k, this threshold has k <= n_k and satisfies
--
--   $$4\binom{k}{2}\binom{n_k-2}{k-2}2^{1-\binom{k}{2}}<1.$$
--
--   Thus the sharp asymptotic scale in Spencer's theorem lies below the local-lemma threshold by any fixed fractional margin.
-- source:
--   J. Spencer, Ramseys theorem - a new lower bound, J. Combin. Theory Ser. A 18 (1975), pp. 108-115, https://doi.org/10.1016/0097-3165(75)90071-0. p. 110, Corollary 2 (Stirling formula applied to Theorem 2).

import Mathlib
open Filter

namespace Erdos77
theorem spencer_1975_lll_asymptotic_threshold (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Eventually (fun k : Nat =>
      2 <= k /\
        k <= Nat.floor
          ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2)) /\
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by sorry
end Erdos77
