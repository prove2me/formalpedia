-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_uniform_edge_coloring_core
-- name    : Erdos77.spencer_1975_uniform_edge_coloring_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T14:21:54.760041+00:00
-- url     : https://prove2.me/theorems/b039e13b-90a7-4c48-9afa-475eea344fa8
-- title:
--   Spencer LLL edge coloring core
-- statement:
--   Under Spencer's symmetric local lemma bound, the edges of the complete graph on n vertices can be colored with two colors so that every k element vertex set contains an edge of each color. This isolates the edge coloring supplied by the probabilistic argument before it is packaged as a SimpleGraph.
-- source:
--   J. Spencer (1975), Ramsey theorem: a new lower bound, J. Combin. Theory Ser. A 18, pp. 108-115, DOI 10.1016/0097-3165(75)90071-0, pp. 109-110, Theorem 2.

import Mathlib

import Mathlib
namespace Erdos77
theorem spencer_1975_uniform_edge_coloring_core (k n : Nat) (hk : 2 <= k)
    (hkn : k <= n)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun (c : Fin n -> Fin n -> Bool) =>
      And (forall a b : Fin n, a != b -> c a b = c b a)
        (forall s : Finset (Fin n), s.card = k ->
          And (Exists fun (a : Fin n) => Exists fun (b : Fin n) => And (Membership.mem s a) (And (Membership.mem s b) (And (a != b) (c a b = true))))
            (Exists fun (a : Fin n) => Exists fun (b : Fin n) => And (Membership.mem s a) (And (Membership.mem s b) (And (a != b) (c a b = false))))) := by sorry
end Erdos77
