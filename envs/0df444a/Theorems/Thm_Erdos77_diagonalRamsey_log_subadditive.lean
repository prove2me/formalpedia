-- Prove2me | Theorems.Thm_Erdos77_diagonalRamsey_log_subadditive
-- name    : Erdos77.diagonalRamsey_log_subadditive
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-26T10:47:20.772988+00:00
-- url     : https://prove2.me/theorems/7f474a9b-ede4-499d-9be2-50d3157b1db6
-- title:
--   Subadditivity of the logarithmic diagonal Ramsey sequence
-- statement:
--   The logarithms of the diagonal Ramsey numbers form a subadditive sequence and are nonnegative, and the diagonal Ramsey numbers are eventually positive. Subadditivity is the combinatorial input that lets Fekete lemma produce a limiting normalized logarithmic growth rate.
-- source:
--   Erdos-Szekeres product inequality for Ramsey numbers, together with the standard finite Ramsey existence and lower-bound arguments; background: https://www.erdosproblems.com/77

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem diagonalRamsey_log_subadditive :
    And (Subadditive (fun k : Nat => Real.log (diagonalRamsey k : Real)))
      (And (forall k : Nat, 0 <= Real.log (diagonalRamsey k : Real))
        (Exists fun N : Nat => forall k : Nat, N <= k ->
          0 < (diagonalRamsey k : Real))) := by sorry
end Erdos77
