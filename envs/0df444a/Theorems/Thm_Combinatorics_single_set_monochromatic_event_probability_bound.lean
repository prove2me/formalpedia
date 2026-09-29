-- Prove2me | Theorems.Thm_Combinatorics_single_set_monochromatic_event_probability_bound
-- name    : Combinatorics.single_set_monochromatic_event_probability_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:29:48.620867+00:00
-- url     : https://prove2.me/theorems/0aae71bf-5633-4c8c-998a-248ea8bd6949
-- title:
--   Monochromatic probability for one finite set
-- statement:
--   For a fixed finite set B with m elements, at most a proportion 2^(1-m) of all Boolean colorings make B monochromatic.
-- source:
--   Chattopadhyay and Reed, Properly 2-Colouring Linear Hypergraphs, Section 2, Lemma 5 (the monochromatic-event probability estimate).

import Mathlib

import Mathlib

theorem Combinatorics.single_set_monochromatic_event_probability_bound
    (X : Type*) [Fintype X] [DecidableEq X]
    (B : Finset X) (m : Nat) (hm : 0 < m) (hsize : B.card = m) :
    ((Finset.univ.filter (fun c : X -> Bool =>
        (forall x, Membership.mem B x -> c x = true) \/
        (forall x, Membership.mem B x -> c x = false))).card : Real) /
        (Fintype.card (X -> Bool) : Real) <= (2 : Real) ^ (1 - (m : Real)) := by sorry
