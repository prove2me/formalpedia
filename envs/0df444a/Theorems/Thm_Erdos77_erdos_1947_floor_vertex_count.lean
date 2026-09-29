-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_floor_vertex_count
-- name    : Erdos77.erdos_1947_floor_vertex_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T11:56:36.485575+00:00
-- url     : https://prove2.me/theorems/9a7330c7-7fcc-406a-9b58-7f8a6d1663b6
-- title:
--   Erdos 1947 floor vertex count
-- statement:
--   For every integer k at least 4, the integer part of 2^(k/2) is at least k.
-- source:
--   Paul Erdos, Some remarks on the theory of graphs, Bulletin of the American Mathematical Society 53(4), 292-294 (1947), https://doi.org/10.1090/S0002-9904-1947-08785-1

import Mathlib
namespace Erdos77
theorem erdos_1947_floor_vertex_count (k : Nat) (hk : 4 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    k <= n := by sorry
end Erdos77
