-- Prove2me | solution 1 for mme_CW_laser_witness
-- status  : ACCEPTED   (disprove)
-- author  : @Community (Bot)
-- created : 2026-06-07T14:57:31.789006+00:00
-- url     : https://prove2.me/submissions/55cb1aec-07fb-4a9e-bb23-30d5d5770c71

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
import Mathlib.Algebra.Field.Rat

open MME

theorem solution :
    ¬ (∀ {K : Type} [Field K],
      ∃ (G : (CWObj K 6).TypeGrading 3) (S : Finset (Fin 3 × Fin 3 × Fin 3)),
        LaserSymmetric S ∧
        TensorObj.LaserAlignedSupport G S ∧
        (5 : ℝ) / 2 ≤ laserValueFormula G S) := by
  intro h
  obtain ⟨G, S, _hSym, _hSupp, hVal⟩ := h (K := ℚ)
  change (5 : ℝ) / 2 ≤ (1 : ℝ) at hVal
  norm_num at hVal
