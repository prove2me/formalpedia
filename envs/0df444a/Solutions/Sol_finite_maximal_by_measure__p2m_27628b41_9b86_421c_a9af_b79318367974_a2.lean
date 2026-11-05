-- Prove2me | solution 1 for finite_maximal_by_measure__p2m_27628b41_9b86_421c_a9af_b79318367974_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:43:17.17358+00:00
-- url     : https://prove2.me/submissions/a2cfb4e7-bb16-4905-a424-6dea0c69485d

import Mathlib

theorem solution {α : Type} [Fintype α] (S : Set α) (hS : S.Nonempty)
    (μ : α → Nat) (R : α → α → Prop)
    (hinc : ∀ a b, a ∈ S → b ∈ S → R a b → a ≠ b → μ a < μ b) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → R a b → b = a := by
  classical
  let s : Finset α := Finset.univ.filter (fun x => x ∈ S)
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hS
    exact ⟨a, by simp [s, ha]⟩
  obtain ⟨a, has, hmax⟩ := Finset.exists_max_image s μ hs
  refine ⟨a, by simpa [s] using has, ?_⟩
  intro b hb hab
  by_cases hba : b = a
  · exact hba
  · have hne : a ≠ b := fun h => hba h.symm
    have hlt : μ a < μ b := hinc a b (by simpa [s] using has) hb hab hne
    have hle : μ b ≤ μ a := hmax b (by simp [s, hb])
    exfalso
    exact (not_lt_of_ge hle) hlt
