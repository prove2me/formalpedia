-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate_ge6
-- name    : Erdos77.erdos_1947_floor_local_lemma_estimate_ge6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:41:13.340014+00:00
-- url     : https://prove2.me/theorems/84153920-7b49-4fee-97db-80867ea89641
-- title:
--   Erdos floor local lemma estimate for k at least 6
-- statement:
--   For every integer k at least 6, let n be the floor of 2^(k/2). Then 4 times binomial(k,2), times binomial(n-2,k-2), times 2^(1-binomial(k,2)) is less than 1. This numerical condition is needed to apply the Lovasz local lemma in Erdos random graph arguments.
-- source:
--   Paul Erdos, Some remarks on the theory of graphs, Bulletin of the American Mathematical Society 53(4), 292-294 (1947), https://doi.org/10.1090/S0002-S0002-9904-1947-08785-1

import Mathlib

namespace Erdos77
theorem erdos_1947_floor_local_lemma_estimate_ge6 (k : Nat) (hk : 6 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by sorry
end Erdos77
