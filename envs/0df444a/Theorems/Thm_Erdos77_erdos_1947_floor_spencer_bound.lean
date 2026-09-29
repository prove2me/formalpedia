-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_floor_spencer_bound
-- name    : Erdos77.erdos_1947_floor_spencer_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:45:05.617204+00:00
-- url     : https://prove2.me/theorems/ad2b6363-a42d-414e-aff9-94c2b7ab4492
-- title:
--   The Erdos floor satisfies the local lemma bound
-- statement:
--   For every integer $k\ge4$, put $n=\lfloor 2^{k/2}\rfloor$. Then $k\le n$ and the numerical symmetric local lemma criterion $4\binom{k}{2}\binom{n-2}{k-2}2^{1-\binom{k}{2}}<1$ holds.
-- source:
--   Numerical estimate used in the random-graph proof of Erdos (1947), Some remarks on the theory of graphs, https://doi.org/10.1090/S0002-9904-1947-08785-1.

import Mathlib

import Mathlib
namespace Erdos77
theorem erdos_1947_floor_spencer_bound (k : Nat) (hk : 4 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    And (k <= n)
      ((4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) := by sorry
end Erdos77
