-- Prove2me | solution 1 for finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:42:51.676203+00:00
-- url     : https://prove2.me/submissions/f15ad6ed-a1d1-44d6-ab91-6060ffd47f8c

import Mathlib

theorem solution
    {V : Type} [Fintype V] (M : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hM : P M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ P N ∧ (∀ Q : SimpleGraph V, N ≤ Q → P Q → Q = N) := by
  let p : SimpleGraph V → Prop := fun N => M ≤ N ∧ P N
  have hpM : p M := ⟨le_rfl, hM⟩
  obtain ⟨N, hMN, hNmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := M) hpM)
  rcases hNmax with ⟨hNp, hNmax'⟩
  refine ⟨N, hNp.1, hNp.2, ?_⟩
  intro Q hNQ hPQ
  exact le_antisymm (hNmax' ⟨hNp.1.trans hNQ, hPQ⟩ hNQ) hNQ
