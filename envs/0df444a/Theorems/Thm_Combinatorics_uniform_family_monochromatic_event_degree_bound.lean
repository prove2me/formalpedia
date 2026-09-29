-- Prove2me | Theorems.Thm_Combinatorics_uniform_family_monochromatic_event_degree_bound
-- name    : Combinatorics.uniform_family_monochromatic_event_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:16:18.010886+00:00
-- url     : https://prove2.me/theorems/2f3733b2-d73e-4d71-9b0f-e52e48d63262
-- title:
--   Dependency degree of monochromatic events
-- statement:
--   Each event in a uniform family has at most mD?1 neighboring events when every point belongs to at most D members.
-- source:
--   Chattopadhyay and Reed, Properly 2-Colouring Linear Hypergraphs, Section 2, Lemma 5 (dependency count).

import Mathlib

theorem Combinatorics.uniform_family_monochromatic_event_degree_bound
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D) :
    (let dep : I -> I -> Prop := fun i j =>
      i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
     (forall i, (Finset.univ.filter (fun j => dep i j)).card <= m * D - 1)) := by sorry
