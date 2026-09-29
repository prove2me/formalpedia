-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate_large
-- name    : Erdos77.erdos_1947_floor_local_lemma_estimate_large
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:14:24.448978+00:00
-- url     : https://prove2.me/theorems/5b67b250-6e4f-48d1-8c41-072ce1551dd2
-- title:
--   Erdos floor local lemma estimate for k at least 5
-- statement:
--   For every integer k at least 5, with n=floor(2^(k/2)), the binomial expression in the Erdos random graph argument is strictly less than 1.
-- source:
--   Paul Erdos, Some remarks on the theory of graphs, Bulletin of the American Mathematical Society 53(4), 292-294 (1947), https://doi.org/10.1090/S0002-S0002-9904-1947-08785-1

import Mathlib

import Mathlib
namespace Erdos77
theorem erdos_1947_floor_local_lemma_estimate_large (k : Nat) (hk : 5 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by sorry
end Erdos77
