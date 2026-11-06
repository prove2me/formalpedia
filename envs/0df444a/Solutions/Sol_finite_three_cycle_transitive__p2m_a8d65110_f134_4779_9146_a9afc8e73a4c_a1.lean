-- Prove2me | solution 1 for finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:59:19.823271+00:00
-- url     : https://prove2.me/submissions/96604518-1a18-4d72-90e0-436ba20c1a4b

-- ID: b4c44d04-edb9-41a7-ac17-6db35041007a | NAME: finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1 | 未本地编译验证
import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (g : α → α)
    (hcard : Fintype.card α = 3)
    (hinj : Function.Injective g)
    (hfixed : ∀ x, g x ≠ x) :
    ∀ x y : α, ∃ k : Nat, g^[k] x = y := by
  classical
  intro x y
  have hxgx : x ≠ g x := (hfixed x).symm
  have hgxg2x : g x ≠ g (g x) := (hfixed (g x)).symm
  have hex : ∃ z : α, z ≠ x ∧ z ≠ g x := by
    by_contra h
    have hsub : Finset.univ ⊆ ({x, g x} : Finset α) := by
      intro w hw
      by_cases hwx : w = x
      · simp [hwx]
      · have hwgx : w = g x := by
          by_contra hwg
          exact h ⟨w, hwx, hwg⟩
        simp [hwgx]
    have hle := Finset.card_le_card hsub
    have hs2 : ({x, g x} : Finset α).card = 2 := by simp [hxgx]
    have : Fintype.card α ≤ 2 := by simpa [hs2] using hle
    omega
  have hg2x_ne_x : g (g x) ≠ x := by
    intro h2
    rcases hex with ⟨z, hzx, hzgx⟩
    have hgz_ne_gx : g z ≠ g x := fun he => hzx (hinj he)
    have hgz_ne_x : g z ≠ x := by
      intro he
      have : g z = g (g x) := he.trans h2.symm
      exact hzgx (hinj this)
    have hall : ∀ w : α, w = x ∨ w = g x ∨ w = z := by
      intro w
      by_contra hw
      simp only [not_or] at hw
      have hxw : x ≠ w := fun he => hw.1 he.symm
      have hgxw : g x ≠ w := fun he => hw.2.1 he.symm
      have hzw : z ≠ w := fun he => hw.2.2 he.symm
      have hxz : x ≠ z := fun he => hzx he.symm
      have hgxz : g x ≠ z := fun he => hzgx he.symm
      let s : Finset α := {x, g x, z, w}
      have hs4 : s.card = 4 := by simp [s, hxgx, hxz, hgxz, hxw, hgxw, hzw]
      have hle : s.card ≤ Fintype.card α := Finset.card_le_univ s
      omega
    rcases hall (g z) with hA | hA | hA
    · exact hgz_ne_x hA
    · exact hgz_ne_gx hA
    · exact hfixed z hA
  have hyall : ∀ w : α, w = x ∨ w = g x ∨ w = g (g x) := by
    intro w
    by_contra hw
    simp only [not_or] at hw
    have hxw : x ≠ w := fun he => hw.1 he.symm
    have hgxw : g x ≠ w := fun he => hw.2.1 he.symm
    have hg2xw : g (g x) ≠ w := fun he => hw.2.2 he.symm
    have hxg2x : x ≠ g (g x) := fun he => hg2x_ne_x he.symm
    let s : Finset α := {x, g x, g (g x), w}
    have hs4 : s.card = 4 := by simp [s, hxgx, hgxg2x, hxg2x, hxw, hgxw, hg2xw]
    have hle : s.card ≤ Fintype.card α := Finset.card_le_univ s
    omega
  rcases hyall y with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simpa using (Function.iterate_succ_apply' g 1 x)⟩
