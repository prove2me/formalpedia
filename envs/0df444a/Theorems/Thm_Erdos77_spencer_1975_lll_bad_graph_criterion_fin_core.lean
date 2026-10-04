-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion_fin_core
-- name    : Erdos77.spencer_1975_lll_bad_graph_criterion_fin_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T13:17:41.263874+00:00
-- url     : https://prove2.me/theorems/d9a7214e-6d46-4b5f-bc07-ef2ce37568f3
-- title:
--   Finite-index Spencer LLL coloring core
-- statement:
--   For k-clique events indexed by the k-element subsets of an n-vertex set, if the symmetric Lovasz local lemma bound is below one, there is a red-blue coloring of the edges of the complete graph on n vertices with no monochromatic k-clique. This is the canonical finite-index probabilistic core used to transfer the result to arbitrary finite vertex types.
-- source:
--   J. Spencer (1975), Ramsey theorem: a new lower bound, J. Combin. Theory Ser. A 18, pp. 108-115, DOI 10.1016/0097-3165(75)90071-0, pp. 109-110, Theorem 2.

import Mathlib

namespace Erdos77
theorem spencer_1975_lll_bad_graph_criterion_fin_core (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      And (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin n) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by sorry
end Erdos77
