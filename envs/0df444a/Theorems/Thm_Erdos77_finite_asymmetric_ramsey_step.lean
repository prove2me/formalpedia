-- Prove2me | Theorems.Thm_Erdos77_finite_asymmetric_ramsey_step
-- name    : Erdos77.finite_asymmetric_ramsey_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T11:56:25.653987+00:00
-- url     : https://prove2.me/theorems/10a9582e-ddb9-4837-ba9e-22fa036ebee9
-- title:
--   Finite asymmetric Ramsey recurrence step
-- statement:
--   If the finite asymmetric Ramsey property holds for the smaller parameter pairs (r?1,s) and (r,s?1), then it holds for (r,s), provided r and s exceed 1. This is the standard vertex-neighborhood recurrence for two-color graph Ramsey numbers.
-- source:
--   The classical Ramsey recurrence R(r,s) ? R(r?1,s) + R(r,s?1), obtained by partitioning the remaining vertices into the neighbors and non-neighbors of one vertex; see P. Erdos and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935), 463-470.

import Mathlib

namespace Erdos77
theorem finite_asymmetric_ramsey_step (r s : Nat) (hr : 1 < r) (hs : 1 < s)
    (h? : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r - 1) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)))
    (h? : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s - 1) ((Compl.compl G).IsClique t))) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)) := by sorry
end Erdos77
