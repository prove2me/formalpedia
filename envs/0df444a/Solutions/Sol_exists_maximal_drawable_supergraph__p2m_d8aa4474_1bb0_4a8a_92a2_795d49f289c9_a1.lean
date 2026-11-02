-- Prove2me | solution 1 for exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:14:07.593958+00:00
-- url     : https://prove2.me/submissions/8407f81f-161b-4c7d-ad46-893996a2ff9d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
import Theorems.Thm_finite_simpleGraph_type__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ K ≤ M ∧
        ∀ J : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn J → M ≤ J → J ≤ M := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let P : SimpleGraph V → Prop := fun M =>
    WilliamsonShmoys.HasPlanarDrawingOn M ∧ K ≤ M
  obtain ⟨M, hPM, hmax⟩ :=
    exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
      P (fun A B => A ≤ B)
      (fun _ => le_rfl)
      (fun _ _ _ hab hbc => le_trans hab hbc)
      ⟨K, hK, le_rfl⟩
  refine ⟨M, hPM.1, hPM.2, ?_⟩
  intro J hJ hMJ
  have hPJ : P J := ⟨hJ, le_trans hPM.2 hMJ⟩
  exact hmax J hPJ hMJ