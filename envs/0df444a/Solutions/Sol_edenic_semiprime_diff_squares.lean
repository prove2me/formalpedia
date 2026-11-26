-- Prove2me | solution 1 for edenic_semiprime_diff_squares
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:13.98834+00:00
-- url     : https://prove2.me/submissions/07b291b6-fa7a-46aa-b253-5968187a1b8e

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∀ u v, u ^ 2 - v ^ 2 = n → v = 1 ∨ (2 * u = n + 1 ∧ 2 * v = n - 1) := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  intro u v hv
  have hpos : 0 < p * (p + 2) := Nat.mul_pos hp.pos hp2.pos
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  have htwo : 2 ≤ p := Nat.Prime.two_le hp
  have hp3 : 3 ≤ p := by omega
  have hge : 3 * 3 ≤ p * (p + 2) := Nat.mul_le_mul hp3 (by omega)
  have hvu : v < u := by
    by_contra hvc
    push_neg at hvc
    have hle : u ^ 2 ≤ v ^ 2 := by
      rw [pow_two, pow_two]
      exact Nat.mul_le_mul hvc hvc
    have h0 : u ^ 2 - v ^ 2 = 0 := Nat.sub_eq_zero_iff_le.mpr hle
    rw [hv] at h0
    omega
  have hpq : (u + v) * (u - v) = p * (p + 2) := by
    rw [← Nat.sq_sub_sq]
    exact hv
  have hpdvd : p ∣ (u + v) * (u - v) := by
    rw [hpq]
    exact Nat.dvd_mul_right p (p + 2)
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with hpa | hpb
  · -- case: p divides u + v
    obtain ⟨s, hs⟩ := exists_eq_mul_right_of_dvd hpa
    have hpq' : (p * s) * (u - v) = p * (p + 2) := by
      rw [← hs]
      exact hpq
    have hpq2 : p * (s * (u - v)) = p * (p + 2) := by
      have hass : p * (s * (u - v)) = (p * s) * (u - v) := by ring
      rw [hass]
      exact hpq'
    have hc : s * (u - v) = p + 2 := Nat.mul_left_cancel hp.pos hpq2
    have hbd : u - v ∣ p + 2 := by
      rw [← hc]
      exact Nat.dvd_mul_left (u - v) s
    rcases Nat.Prime.eq_one_or_self_of_dvd hp2 (u - v) hbd with hb | hb
    · -- u - v = 1
      rw [hb] at hpq
      right
      omega
    · -- u - v = p + 2, impossible
      rw [hb] at hpq
      have hcomm : (p + 2) * (u + v) = (p + 2) * p := by
        rw [← Nat.mul_comm (u + v) (p + 2), ← Nat.mul_comm p (p + 2)]
        exact hpq
      have ha : u + v = p := Nat.mul_left_cancel hp2.pos hcomm
      omega
  · -- case: p divides u - v
    obtain ⟨s, hs⟩ := exists_eq_mul_right_of_dvd hpb
    rw [hs, Nat.mul_left_comm (u + v) p s] at hpq
    have hc : (u + v) * s = p + 2 := Nat.mul_left_cancel hp.pos hpq
    have hsd : s ∣ p + 2 := by
      rw [← hc]
      exact Nat.dvd_mul_left s (u + v)
    rcases Nat.Prime.eq_one_or_self_of_dvd hp2 s hsd with hs1 | hs2
    · -- s = 1, so u - v = p
      rw [hs1] at hs
      rw [hs1] at hc
      omega
    · -- s = p + 2, impossible
      rw [hs2] at hs
      rw [hs2] at hc
      have hcomm : (p + 2) * (u + v) = (p + 2) * 1 := by
        rw [Nat.mul_comm (p + 2) (u + v), Nat.mul_one (p + 2)]
        exact hc
      have ha : u + v = 1 := Nat.mul_left_cancel hp2.pos hcomm
      omega
