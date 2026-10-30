-- Prove2me | solution 1 for exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:39.757616+00:00
-- url     : https://prove2.me/submissions/ed40a8c9-6df7-49d3-8c35-1643626a9073

import Mathlib
import Theorems.Thm_exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
import Theorems.Thm_finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : P M) :
    ∃ T : SimpleGraph V, M ≤ T ∧ P T ∧
      (∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T) := by
  classical
  letI : Finite (SimpleGraph V) :=
    finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1 (V := V)
  let s : Set (SimpleGraph V) := {T | M ≤ T ∧ P T}
  have hs : s.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨T, hTs, hmax⟩ :=
    exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1 s hs
  refine ⟨T, ?_, ?_, ?_⟩
  · exact hTs.1
  · exact hTs.2
  · intro U hTU hPU
    apply hmax U ⟨le_trans hTs.1 hTU, hPU⟩ hTU