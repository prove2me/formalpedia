-- Prove2me | solution 1 for fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:13:44.270793+00:00
-- url     : https://prove2.me/submissions/1b9c4ebf-3518-4f05-a009-78960459da1e

import Mathlib

theorem solution {α : Type} [Fintype α] (hcard : Fintype.card α = 2)
    (x y : α) (hxy : x ≠ y) : ∀ z : α, z = x ∨ z = y := by
  classical
  intro z
  by_contra hz
  simp only [not_or] at hz
  have hxz : x ≠ z := fun h => hz.1 h.symm
  have hyz : y ≠ z := fun h => hz.2 h.symm
  let s : Finset α := {x, y, z}
  have hs3 : s.card = 3 := by
    simp [s, hxy, hxz, hyz]
  have hle : s.card ≤ Fintype.card α := Finset.card_le_univ s
  omega
