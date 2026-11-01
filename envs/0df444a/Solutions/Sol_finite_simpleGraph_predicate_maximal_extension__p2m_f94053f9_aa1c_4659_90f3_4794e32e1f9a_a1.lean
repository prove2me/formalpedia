-- Prove2me | solution 1 for finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:34.087673+00:00
-- url     : https://prove2.me/submissions/c050ecb0-df70-4175-bd30-4191caf5b26b

import Mathlib

set_option autoImplicit false

open Set

theorem solution
    {U : Type} [Fintype U]
    (H : SimpleGraph U) (P : SimpleGraph U → Prop) (hP : P H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph U, K ≤ L → P L → K = L := by
  classical
  let S : Set (SimpleGraph U) := {K | H ≤ K ∧ P K}
  have hfinite : S.Finite := Set.toFinite S
  have hnonempty : S.Nonempty := ⟨H, le_rfl, hP⟩
  obtain ⟨K, hK, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hPL
  have hL : L ∈ S := ⟨hK.1.trans hKL, hPL⟩
  exact le_antisymm hKL (hmax hL hKL)