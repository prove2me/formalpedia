-- Prove2me | solution 1 for finite_exists_maximal_extension__p2m_2521a354_9295_4d68_a93a_2d2a5f622a67_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:58.184928+00:00
-- url     : https://prove2.me/submissions/ac4bbceb-fa2e-4e5c-8871-cd0a4d0fde55

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (hM : P M) :
    Exists fun N : SimpleGraph V => And (LE.le M N) (And (P N)
      (forall K : SimpleGraph V, LE.le N K -> P K -> K = N)) := by
  classical
  let Q : SimpleGraph V → Prop := fun K => P K ∧ M ≤ K
  obtain ⟨N, hMN, hNmax⟩ :=
    Finite.exists_le_maximal (p := Q) (a := M) (show Q M from ⟨hM, le_rfl⟩)
  refine ⟨N, hMN, hNmax.1.1, ?_⟩
  intro K hNK hPK
  have hQK : Q K := ⟨hPK, hMN.trans hNK⟩
  exact le_antisymm (hNmax.2 hQK hNK) hNK