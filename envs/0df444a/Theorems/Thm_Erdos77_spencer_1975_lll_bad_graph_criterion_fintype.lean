-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion_fintype
-- name    : Erdos77.spencer_1975_lll_bad_graph_criterion_fintype
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:46:09.659986+00:00
-- url     : https://prove2.me/theorems/e262c3a8-bf91-4336-9203-119bb1623cda
-- title:
--   Spencer 1975 LLL criterion for finite vertex types
-- statement:
--   For every finite vertex type V, if the symmetric local-lemma bound using |V| and the number of k-sets containing a fixed edge is below 1, then V admits a two-coloring of its edges with no monochromatic k-clique.
-- source:
--   J. Spencer (1975), Ramsey theorem: a new lower bound, J. Combin. Theory Ser. A 18, pp. 108-115, DOI 10.1016/0097-3165(75)90071-0, pp. 109-110, Theorem 2.

import Mathlib

namespace Erdos77
theorem spencer_1975_lll_bad_graph_criterion_fintype (V : Type*) [Fintype V] [DecidableEq V]
    (k : Nat) (hk : 2 <= k) (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) *
          (Nat.choose (Fintype.card V - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph V =>
      And (Not (Exists fun s : Finset V => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset V => And (s.card = k) ((Compl.compl G).IsClique s))) := by sorry
end Erdos77
