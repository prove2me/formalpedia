-- Prove2me | solution 1 for edenic_semiprime_no_primitive_root
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:29.454211+00:00
-- url     : https://prove2.me/submissions/172f379a-90c5-4eee-b467-ea4a7fab8e65

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  intro hg
  obtain ⟨g, hg'⟩ := hg
  have h0 : 0 < p * (p + 2) := Nat.mul_pos hp.pos hp2.pos
  haveI : NeZero (p * (p + 2)) := ⟨ne_of_gt h0⟩
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  have htwo : 2 ≤ p := Nat.Prime.two_le hp
  have hpodd : Odd p := (hp.eq_two_or_odd').resolve_left hne2
  have hp2odd : Odd (p + 2) := by
    obtain ⟨t, ht⟩ := hpodd
    exact ⟨t + 1, by omega⟩
  have hpne1 : p ≠ 1 := Nat.Prime.ne_one hp
  have hp2ne1 : p + 2 ≠ 1 := fun h => by omega
  have hcop : p.Coprime (p + 2) := twin_primes_coprime p hp hp2
  have hkpos : 0 < Nat.totient (p * (p + 2)) := Nat.totient_pos.mpr h0
  have hk0 : Nat.totient (p * (p + 2)) ≠ 0 := ne_of_gt hkpos
  have hcu : IsPrimitiveRoot ((hg'.isUnit hk0).unit) (Nat.totient (p * (p + 2))) :=
    IsPrimitiveRoot.isUnit_unit hk0 hg'
  have hord : orderOf ((hg'.isUnit hk0).unit) =
      Nat.card (ZMod (p * (p + 2)))ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        ← IsPrimitiveRoot.eq_orderOf hcu]
  have hcyc : IsCyclic (ZMod (p * (p + 2)))ˣ :=
    isCyclic_of_orderOf_eq_card ((hg'.isUnit hk0).unit) hord
  exact (ZMod.not_isCyclic_units_of_mul_coprime p (p + 2) hpodd hpne1 hp2odd hp2ne1
    hcop) hcyc

-- #47
