-- Prove2me | Theorems.Thm_Erdos77_diagonalRamsey_product_graph_property
-- name    : Erdos77.diagonalRamsey_product_graph_property
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-26T12:43:23.610729+00:00
-- url     : https://prove2.me/theorems/6b543a7b-6df9-4c9e-801f-9ec36dfb0c23
-- title:
--   Finite graph form of the Ramsey product inequality
-- statement:
--   For positive integers m and n, every graph on $$R(m)R(n)$$ vertices contains a clique of size $$m+n$$ or an independent set of size $$m+n$$. Here $$R(k)$$ denotes the diagonal Ramsey number, so the statement isolates the finite coloring assertion behind the product bound.
-- source:
--   Erdos-Szekeres product inequality for Ramsey numbers; https://www.erdosproblems.com/77

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

namespace Erdos77
theorem diagonalRamsey_product_graph_property (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    forall G : SimpleGraph (Fin (diagonalRamsey m * diagonalRamsey n)),
      Or
        (Exists fun s : Finset (Fin (diagonalRamsey m * diagonalRamsey n)) =>
          G.IsNClique (m + n) s)
        (Exists fun s : Finset (Fin (diagonalRamsey m * diagonalRamsey n)) =>
          (Compl.compl G).IsNClique (m + n) s) := by sorry
end Erdos77
