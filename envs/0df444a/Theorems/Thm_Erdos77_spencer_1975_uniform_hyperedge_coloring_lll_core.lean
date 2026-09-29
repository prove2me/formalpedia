-- Prove2me | Theorems.Thm_Erdos77_spencer_1975_uniform_hyperedge_coloring_lll_core
-- name    : Erdos77.spencer_1975_uniform_hyperedge_coloring_lll_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T17:57:45.318726+00:00
-- url     : https://prove2.me/theorems/2d302b33-a1d0-4575-8534-691148a2fbb8
-- title:
--   Spencer LLL core for uniform hyperedge colorings
-- statement:
--   Let V be a finite set, and let 1 ? r ? k ? |V|. Color every r-element subset of V red or blue. If
--
--   $$4\binom{k}{r}\binom{|V|-r}{k-r}2^{1-\binom{k}{r}}<1,$$
--
--   then there is a coloring in which every k-element subset contains an r-element subset of each color. The symmetric Lovasz local lemma applies to the events that a fixed k-set is monochromatic.
-- source:
--   Joel Spencer, Ramsey's theorem - a new lower bound, Journal of Combinatorial Theory, Series A 18 (1975), 108-115, Section 1, https://doi.org/10.1016/0097-3165(75)90071-0

import Mathlib

import Mathlib
namespace Erdos77

theorem spencer_1975_uniform_hyperedge_coloring_lll_core (V : Type*) [Fintype V]
    [DecidableEq V] (r k : Nat) (hr : 1 <= r) (hrk : r <= k)
    (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k r : Real) *
          (Nat.choose (Fintype.card V - r) (k - r) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k r : Real)) < 1) :
    Exists fun c : {e : Finset V // e.card = r} -> Bool =>
      forall s : Finset V, s.card = k ->
        And
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = true))
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = false)) := by sorry

end Erdos77
