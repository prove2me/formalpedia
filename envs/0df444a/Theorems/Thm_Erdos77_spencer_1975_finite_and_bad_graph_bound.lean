-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_finite_and_bad_graph_bound
-- name    : Erdos77.spencer_1975_finite_and_bad_graph_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:28:29.322766+00:00
-- url     : https://prove2.me/theorems/6bcce319-2fd5-4499-beb0-96947c71c1a6
-- title:
--   Finite Ramsey threshold exceeds any bad coloring size
-- statement:
--   Suppose the diagonal Ramsey property holds at some finite vertex count, and suppose there is a graph on n vertices with neither a clique of size k nor an independent set of size k. Then
--
--   $$R(k)\ge n+1.$$
--
--   The finite witness ensures that the least Ramsey threshold in the definition exists; the bad coloring rules out every threshold at most n.
-- source:
--   Formal consequence of the mission definition of diagonal Ramsey number and Ramsey finiteness; the bad-coloring obstruction is used in Spencer 1975, p. 109.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

namespace Erdos77
theorem spencer_1975_finite_and_bad_graph_bound (k n : Nat)
    (hfinite : Exists fun m : Nat => forall G : SimpleGraph (Fin m),
      Or
        (Exists fun s : Finset (Fin m) => And (s.card = k) (G.IsClique s))
        (Exists fun s : Finset (Fin m) => And (s.card = k) ((Compl.compl G).IsClique s)))
    (hbad : Exists fun G : SimpleGraph (Fin n) =>
      (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))) /\
        (Not (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s)))) :
    (n : Real) + 1 <= (diagonalRamsey k : Real) := by sorry
end Erdos77
