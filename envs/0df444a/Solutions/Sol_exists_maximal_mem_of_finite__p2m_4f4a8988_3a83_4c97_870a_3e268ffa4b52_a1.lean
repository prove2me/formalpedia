-- Prove2me | solution 1 for exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:36.691836+00:00
-- url     : https://prove2.me/submissions/8ea6243f-7c19-44c7-808b-5d0ac785a873

import Mathlib

set_option autoImplicit false

theorem solution
    {alpha : Type} [Fintype alpha] [PartialOrder alpha]
    (P : alpha -> Prop)
    (hne : exists a, P a) :
    exists a, P a /\ forall b, a <= b -> P b -> b = a := by
  classical
  rcases hne with ⟨x, hx⟩
  obtain ⟨a, ha, hmax⟩ :=
    (Set.toFinite ({a : alpha | P a} : Set alpha)).exists_maximal ⟨x, hx⟩
  change P a at ha
  refine ⟨a, ha, ?_⟩
  intro b hab hb
  have hba : b <= a := hmax hb hab
  exact (le_antisymm hab hba).symm
