-- Prove2me | solution 1 for finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:26.164466+00:00
-- url     : https://prove2.me/submissions/45f41562-0d0d-458b-a515-cbb7814ae42d

import Mathlib
set_option autoImplicit false

theorem solution {Alpha : Type} [Fintype Alpha] [DecidableEq Alpha]
    (s : Finset Alpha) (r : Alpha -> Alpha -> Prop) (hne : s.Nonempty)
    (hirr : forall a, Not (r a a))
    (htrans : forall a b c, r a b -> r b c -> r a c) :
    Exists (fun a => And (Membership.mem s a)
      (forall b, Membership.mem s b -> Not (r a b))) := by
  classical
  have aux : forall n : Nat, forall t : Finset Alpha, t.card = n -> t.Nonempty ->
      Exists (fun a => And (Membership.mem t a)
        (forall b, Membership.mem t b -> Not (r a b))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t hcard htne
        obtain ⟨x, hx⟩ := htne
        by_cases hs : Exists (fun y => And (Membership.mem t y) (r x y))
        · obtain ⟨y, hy, hxy⟩ := hs
          have hyx : y ≠ x := by
            intro heq
            subst y
            exact hirr x hxy
          let u := t.erase x
          have hucard : u.card < n := by
            dsimp [u]
            rw [← hcard]
            exact Finset.card_erase_lt_of_mem hx
          have hune : u.Nonempty := by
            exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩
          obtain ⟨q, hqu, hq⟩ := ih u.card hucard u rfl hune
          refine ⟨q, (Finset.mem_erase.mp hqu).2, ?_⟩
          intro b hb hqb
          by_cases hbx : b = x
          · subst b
            have hyu : Membership.mem u y := Finset.mem_erase.mpr ⟨hyx, hy⟩
            exact hq y hyu (htrans q x y hqb hxy)
          · exact hq b (Finset.mem_erase.mpr ⟨hbx, hb⟩) hqb
        · exact ⟨x, hx, by
            intro b hb hxb
            exact hs ⟨b, hb, hxb⟩⟩
  exact aux s.card s rfl hne