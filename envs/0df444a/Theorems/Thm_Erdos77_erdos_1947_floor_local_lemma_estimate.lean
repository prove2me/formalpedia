-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate
-- name    : Erdos77.erdos_1947_floor_local_lemma_estimate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T11:56:37.639301+00:00
-- url     : https://prove2.me/theorems/bc515432-a91b-46f4-b0a0-bbdf0f603e52
-- title:
--   Erdos 1947 floor local lemma estimate
-- statement:
--   For every integer k at least 4, with n=floor(2^(k/2)), the binomial expression in the Erdos random graph argument is strictly less than 1.
-- source:
--   Paul Erdos, Some remarks on the theory of graphs, Bulletin of the American Mathematical Society 53(4), 292-294 (1947), https://doi.org/10.1090/S0002-9904-1947-08785-1

import Mathlib
namespace Erdos77
theorem erdos_1947_floor_local_lemma_estimate (k : Nat) (hk : 4 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by sorry
end Erdos77
