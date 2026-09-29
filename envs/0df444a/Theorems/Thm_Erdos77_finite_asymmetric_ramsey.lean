-- Prove2me | Theorems.Thm_Erdos77_finite_asymmetric_ramsey
-- name    : Erdos77.finite_asymmetric_ramsey
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:41:42.792986+00:00
-- url     : https://prove2.me/theorems/63c27a5a-8b97-49e0-9ebf-b47cde947acc
-- title:
--   Finite asymmetric graph Ramsey theorem
-- statement:
--   For every pair of positive integers r and s, there is a finite number n such that every simple graph on n vertices contains either an r-vertex clique or an s-vertex clique in its complement.
-- source:
--   P. Erdos and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935), 463-470, http://www.numdam.org/item/CM_1935__2__463_0/

import Mathlib

namespace Erdos77
theorem finite_asymmetric_ramsey (r s : Nat) (hr : 1 <= r) (hs : 1 <= s) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)) := by sorry
end Erdos77
