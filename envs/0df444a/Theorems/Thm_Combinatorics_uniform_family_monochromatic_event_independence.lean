-- Prove2me | Theorems.Thm_Combinatorics_uniform_family_monochromatic_event_independence
-- name    : Combinatorics.uniform_family_monochromatic_event_independence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T20:16:16.513087+00:00
-- url     : https://prove2.me/theorems/7dc4b8e2-ed2e-4353-805d-61441b290b0c
-- title:
--   Independence from non-neighbor avoidance
-- statement:
--   For an edge i, its monochromatic event is independent of joint avoidance of any finite set S of events whose supports are disjoint from that edge.
-- source:
--   Chattopadhyay and Reed, Properly 2-Colouring Linear Hypergraphs, Section 2, Lemma 5 (product-space independence).

import Mathlib

theorem Combinatorics.uniform_family_monochromatic_event_independence
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D) :
    (let A : I -> Finset (X -> Bool) := fun i =>
      Finset.univ.filter (fun c =>
        (forall x, Membership.mem (B i) x -> c x = true) \/
        (forall x, Membership.mem (B i) x -> c x = false))
     let dep : I -> I -> Prop := fun i j =>
       i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
     (forall (i : I) (S : Finset I),
       (forall j, Membership.mem S j -> Not (dep i j)) ->
       ((Finset.filter (fun w => Membership.mem (A i) w)
           (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w)))).card : Real) /
           (Fintype.card (X -> Bool) : Real) =
         (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w))).card : Real) /
             (Fintype.card (X -> Bool) : Real)) *
           ((A i).card : Real) / (Fintype.card (X -> Bool) : Real))) := by sorry
