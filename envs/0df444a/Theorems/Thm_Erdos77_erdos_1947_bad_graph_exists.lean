-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_bad_graph_exists
-- name    : Erdos77.erdos_1947_bad_graph_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T09:59:55.063665+00:00
-- url     : https://prove2.me/theorems/6c7fe293-2474-40ab-9099-b5aa94c2bc5c
-- title:
--   A graph with no monochromatic k-clique at floor(2^(k/2)) vertices
-- statement:
--   For every k >= 3, there is a simple graph on floor(2^(k/2)) labeled vertices with neither a clique nor an independent set of size k. Erdos proves this by counting: the expected number of monochromatic k-sets in a uniformly random graph is less than one.
-- source:
--   P. Erdos, Some remarks on the theory of graphs, Bull. Amer. Math. Soc. 53 (1947), 292-294, https://doi.org/10.1090/S0002-9904-1947-08785-1

import Mathlib

namespace Erdos77
theorem erdos_1947_bad_graph_exists (k : Nat) (hk : 3 <= k) :
    Exists fun G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
      And
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by sorry
end Erdos77
