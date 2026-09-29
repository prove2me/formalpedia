-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_finite_and_bad_graph_bound
-- name    : Erdos77.erdos_1947_finite_and_bad_graph_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:00:07.487997+00:00
-- url     : https://prove2.me/theorems/3bdee47b-f622-47af-a8b3-8e6d3baac5b3
-- title:
--   A finite Ramsey threshold and a bad graph give the 1947 lower bound
-- statement:
--   If some finite order has the Ramsey property and there is a graph on floor(2^(k/2)) vertices with no monochromatic k-set, then the least Ramsey threshold is strictly larger than 2^(k/2). Finiteness ensures the infimum defining the threshold is attained; the bad graph rules out every smaller threshold by restriction.
-- source:
--   Definition Erdos77.diagonalRamsey in the Erdos Problem 77 mission

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

namespace Erdos77
theorem erdos_1947_finite_and_bad_graph_bound (k : Nat) (hk : 3 <= k)
    (hfinite : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))
        (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s)))
    (hbad : Exists fun G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
      And
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) ((Compl.compl G).IsClique s)))) :
    (2 : Real) ^ ((k : Real) / 2) < (diagonalRamsey k : Real) := by sorry
end Erdos77
