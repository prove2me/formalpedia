-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_ramsey_finiteness
-- name    : Erdos77.erdos_1947_ramsey_finiteness
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T09:59:56.788719+00:00
-- url     : https://prove2.me/theorems/31c9dc87-173d-40ea-83f8-3089375876ce
-- title:
--   Finiteness of the diagonal Ramsey threshold
-- statement:
--   For every positive k, there is a finite number of vertices such that every simple graph on that many labeled vertices has either a k-clique or an independent k-set. This finiteness fact is needed because diagonalRamsey is an infimum, with value zero if its defining set is empty.
-- source:
--   P. Erdos and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935), 463-470, http://www.numdam.org/item/CM_1935__2__463_0/

import Mathlib

namespace Erdos77
theorem erdos_1947_ramsey_finiteness (k : Nat) (hk : 1 <= k) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))
        (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s)) := by sorry
end Erdos77
