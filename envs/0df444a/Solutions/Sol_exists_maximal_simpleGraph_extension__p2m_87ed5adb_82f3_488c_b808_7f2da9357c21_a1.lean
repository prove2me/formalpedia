-- Prove2me | solution 1 for exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:46.28633+00:00
-- url     : https://prove2.me/submissions/ff5e2be0-e224-4c16-a07c-22e4a4fce220

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let s : Set (SimpleGraph V) := {G | L ≤ G ∧ P G}
  have hs : s.Nonempty := ⟨L, le_rfl, hP⟩
  obtain ⟨H, hHs, hmax⟩ := s.toFinite.exists_maximal hs
  refine ⟨H, hHs.1, hHs.2, ?_⟩
  intro K hHK hPK
  have hKs : K ∈ s := ⟨hHs.1.trans hHK, hPK⟩
  have hKH : K ≤ H := hmax hKs hHK
  exact le_antisymm hKH hHK