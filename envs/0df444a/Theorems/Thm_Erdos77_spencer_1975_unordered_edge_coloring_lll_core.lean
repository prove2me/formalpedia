-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_unordered_edge_coloring_lll_core
-- name    : Erdos77.spencer_1975_unordered_edge_coloring_lll_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T17:45:29.136006+00:00
-- url     : https://prove2.me/theorems/c405300a-8355-4435-bd14-412a8686197a
-- title:
--   Spencer LLL core on unordered edges
-- statement:
--   Let $V$ be a finite vertex set and let $2\le k\le |V|$. Color each unordered two-element subset of $V$ red or blue. If
--
--   $$
--   4\binom{k}{2}\binom{|V|-2}{k-2}2^{1-\binom{k}{2}}<1,
--   $$
--
--   then there is such a coloring for which every $k$-element subset contains an edge of each color. Equivalently, no $k$-element vertex set is monochromatic.
--
--   This is the finite probabilistic core of Spencer's local-lemma argument, stated on unordered edges so that graph construction and ordered-pair symmetry are separate deterministic consequences.
--
--   **Formalization Note** An unordered edge is represented by a finite subset carrying a proof that its cardinality is two.
-- source:
--   Joel Spencer, 'Ramsey's theorem--a new lower bound,' Journal of Combinatorial Theory, Series A 18 (1975), 108-115, Section 1, https://doi.org/10.1016/0097-3165(75)90071-0

import Mathlib

namespace Erdos77

theorem spencer_1975_unordered_edge_coloring_lll_core (V : Type*) [Fintype V]
    [DecidableEq V] (k : Nat) (hk : 2 <= k) (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) *
          (Nat.choose (Fintype.card V - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun c : {e : Finset V // e.card = 2} -> Bool =>
      forall s : Finset V, s.card = k ->
        And
          (Exists fun e : {e : Finset V // e.card = 2} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v)
              (c e = true))
          (Exists fun e : {e : Finset V // e.card = 2} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v)
              (c e = false)) := by sorry

end Erdos77
