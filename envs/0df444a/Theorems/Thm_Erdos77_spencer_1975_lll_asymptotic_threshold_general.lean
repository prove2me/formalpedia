-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_lll_asymptotic_threshold_general
-- name    : Erdos77.spencer_1975_lll_asymptotic_threshold_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:44:20.579921+00:00
-- url     : https://prove2.me/theorems/2f296b16-9572-43d8-b7e9-d15beb6d26b2
-- title:
--   Asymptotic LLL threshold below the Spencer constant
-- statement:
--   For every fixed real constant c with 0 < c < 1, put n_k = floor(c * (sqrt 2 / e) * k * 2^(k/2)). For all sufficiently large k, one has 2 <= k <= n_k and the symmetric local lemma expression 4 * choose(k,2) * choose(n_k-2,k-2) * 2^(1-choose(k,2)) is less than 1. This parameterized form isolates the asymptotic estimate used in the 1975 lower bound for diagonal Ramsey numbers.
-- source:
--   J. Spencer, Ramseys theorem - a new lower bound, J. Combin. Theory Ser. A 18 (1975), pp. 108-115, https://doi.org/10.1016/0097-3165(75)90071-0, p. 110, Corollary 2.

import Mathlib
open Filter

namespace Erdos77
theorem spencer_1975_lll_asymptotic_threshold_general (c : Real) (hc : 0 < c) (hc1 : c < 1) :
    Filter.Eventually (fun k : Nat =>
      2 <= k /\
        k <= Nat.floor
          (c * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2)) /\
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                (c * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by sorry
end Erdos77
