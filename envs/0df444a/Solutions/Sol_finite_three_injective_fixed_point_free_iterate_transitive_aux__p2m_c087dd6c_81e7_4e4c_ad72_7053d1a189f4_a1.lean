-- Prove2me | solution 1 for finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:02:29.0992+00:00
-- url     : https://prove2.me/submissions/f6d53c47-7f8d-4892-b1a4-ec43e9f8d342

import Mathlib
set_option autoImplicit false
-- ID: b4c44d04-edb9-41a7-ac17-6db35041007a | NAME: finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1 | 未本地编译验证

theorem solution {α : Type} [Fintype α] (f : α → α)
    (hcard : Fintype.card α = 3)
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, ∃ k : Nat, f^[k] x = y := by
  classical
  intro x y
  have hxgx : x ≠ f x := (hfixed x).symm
  have hgxg2x : f x ≠ f (f x) := (hfixed (f x)).symm
  have hex : ∃ z : α, z ≠ x ∧ z ≠ f x := by
    by_contra h
    have hsub : Finset.univ ⊆ ({x, f x} : Finset α) := by
      intro w hw
      by_cases hwx : w = x
      · simp [hwx]
      · have hwgx : w = f x := by
          by_contra hwg
          exact h ⟨w, hwx, hwg⟩
        simp [hwgx]
    have hle := Finset.card_le_card hsub
    have hs2 : ({x, f x} : Finset α).card = 2 := by simp [hxgx]
    have : Fintype.card α ≤ 2 := by simpa [hs2] using hle
    omega
  have hg2x_ne_x : f (f x) ≠ x := by
    intro h2
    rcases hex with ⟨z, hzx, hzgx⟩
    have hgz_ne_gx : f z ≠ f x := fun he => hzx (hinj he)
    have hgz_ne_x : f z ≠ x := by
      intro he
      have : f z = f (f x) := he.trans h2.symm
      exact hzgx (hinj this)
    have hall : ∀ w : α, w = x ∨ w = f x ∨ w = z := by
      intro w
      by_contra hw
      simp only [not_or] at hw
      have hxw : x ≠ w := fun he => hw.1 he.symm
      have hgxw : f x ≠ w := fun he => hw.2.1 he.symm
      have hzw : z ≠ w := fun he => hw.2.2 he.symm
      have hxz : x ≠ z := fun he => hzx he.symm
      have hgxz : f x ≠ z := fun he => hzgx he.symm
      let s : Finset α := {x, f x, z, w}
      have hs4 : s.card = 4 := by simp [s, hxgx, hxz, hgxz, hxw, hgxw, hzw]
      have hle : s.card ≤ Fintype.card α := Finset.card_le_univ s
      omega
    rcases hall (f z) with hA | hA | hA
    · exact hgz_ne_x hA
    · exact hgz_ne_gx hA
    · exact hfixed z hA
  have hyall : ∀ w : α, w = x ∨ w = f x ∨ w = f (f x) := by
    intro w
    by_contra hw
    simp only [not_or] at hw
    have hxw : x ≠ w := fun he => hw.1 he.symm
    have hgxw : f x ≠ w := fun he => hw.2.1 he.symm
    have hg2xw : f (f x) ≠ w := fun he => hw.2.2 he.symm
    have hxg2x : x ≠ f (f x) := fun he => hg2x_ne_x he.symm
    let s : Finset α := {x, f x, f (f x), w}
    have hs4 : s.card = 4 := by simp [s, hxgx, hgxg2x, hxg2x, hxw, hgxw, hg2xw]
    have hle : s.card ≤ Fintype.card α := Finset.card_le_univ s
    omega
  rcases hyall y with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simpa using (Function.iterate_succ_apply' f 1 x)⟩
