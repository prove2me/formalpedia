-- Prove2me | solution 1 for edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:38:47.92834+00:00
-- url     : https://prove2.me/submissions/441a50a9-7ddd-46e2-9143-7030a7fca18f

import Mathlib
set_option autoImplicit false

theorem edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel L.Adj := dL;
    (∑ s ∈ C, {e ∈ L.edgeFinset | e.toFinset ⊆ s}.card) = L.edgeFinset.card) := by
  letI : DecidableRel L.Adj := dL
  show (∑ s ∈ C, {e ∈ L.edgeFinset | e.toFinset ⊆ s}.card) = L.edgeFinset.card
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : L.Adj u v := he
    obtain ⟨s, hs, hu, hv⟩ := hpair u v hadj
    have hsub : (s(u, v) : Sym2 V).toFinset ⊆ s := by
      intro x hx
      simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    rw [Finset.sum_eq_single_of_mem s hs]
    · simp [hsub]
    · intro t ht hts
      have hd := hdisj t ht s hs hts
      have hut : u ∉ t := fun hut => Finset.disjoint_left.mp hd hut hu
      have : ¬ (s(u, v) : Sym2 V).toFinset ⊆ t := by
        intro h
        exact hut (h (by simp))
      simp [this]

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel L.Adj := dL;
    (∑ s ∈ C, {e ∈ L.edgeFinset | e.toFinset ⊆ s}.card) = L.edgeFinset.card) :=
  edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1 L dL C hdisj hpair
