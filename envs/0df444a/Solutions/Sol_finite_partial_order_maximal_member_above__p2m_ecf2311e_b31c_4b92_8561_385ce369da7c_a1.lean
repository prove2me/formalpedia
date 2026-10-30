-- Prove2me | solution 1 for finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:58.997167+00:00
-- url     : https://prove2.me/submissions/cc1e815e-b926-4c33-b7d0-a59a4967b51f

import Mathlib

set_option autoImplicit false

theorem solution
    {alpha : Type} [Fintype alpha] [PartialOrder alpha]
    (P : alpha -> Prop) {a : alpha} (ha : P a) :
    Exists fun b : alpha => And (LE.le a b)
      (And (P b) (forall c : alpha, P c -> LE.le b c -> c = b)) := by
  obtain ⟨b, hab, hb, hmax⟩ :=
    Finite.exists_le_maximal (p := P) (a := a) ha
  refine ⟨b, hab, hb, ?_⟩
  intro c hc hbc
  exact le_antisymm (hmax hc hbc) hbc