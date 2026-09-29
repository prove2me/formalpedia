-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_threshold_lll_estimate
-- name    : Erdos77.spencer_1975_threshold_lll_estimate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T14:04:36.857868+00:00
-- url     : https://prove2.me/theorems/a4a7823b-9c35-4551-a17b-0395615d1ffa
-- title:
--   Stirling estimate for Spencer's LLL threshold
-- statement:
--   For each fixed $0 < \varepsilon < 1$, Stirling's formula implies that the symmetric local-lemma expression at $n_k=\lfloor(1-\varepsilon)(\sqrt{2}/e)k2^{k/2}\rfloor$ is eventually less than 1. The fixed fractional loss gives exponential decay in the logarithm of the bound.
-- source:
--   J. Spencer, Ramsey's theorem: a new lower bound, J. Combin. Theory Ser. A 18 (1975), pp. 108-115, p. 110, Corollary 2 (Stirling formula applied to Theorem 2).

import Mathlib
open Filter

namespace Erdos77
theorem spencer_1975_threshold_lll_estimate (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Eventually (fun k : Nat =>
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by sorry
end Erdos77
