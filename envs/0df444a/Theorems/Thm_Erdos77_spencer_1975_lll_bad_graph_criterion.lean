-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion
-- name    : Erdos77.spencer_1975_lll_bad_graph_criterion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:27:34.184124+00:00
-- url     : https://prove2.me/theorems/de36bcb7-6135-4a22-a60f-884f5199cb50
-- title:
--   Spencer 1975 - Lovasz local lemma coloring criterion
-- statement:
--   Let k and n be integers with 2 <= k <= n. If
--
--   $$4\binom{k}{2}\binom{n-2}{k-2}2^{1-\binom{k}{2}} < 1,$$
--
--   then there is a graph on n vertices with no clique or independent set of size k. This is the symmetric local-lemma condition used in Spencer's proof.
-- source:
--   J. Spencer, Ramseys theorem - a new lower bound, J. Combin. Theory Ser. A 18 (1975), pp. 108-115, https://doi.org/10.1016/0097-3165(75)90071-0. pp. 109-110, Theorem 2.

import Mathlib

namespace Erdos77
theorem spencer_1975_lll_bad_graph_criterion (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s))) /\
        (Not (Exists fun s : Finset (Fin n) => And (s.card = k) ((Compl.compl G).IsClique s))) := by sorry
end Erdos77
