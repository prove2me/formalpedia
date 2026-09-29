-- Prove2me | solution 1 for mme_dwz_table2_component_endpoint_product_eq_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:10:06.716697+00:00
-- url     : https://prove2.me/submissions/77ab8ad9-c36d-45c4-b189-ed8af73ae7ec

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open BigOperators Finset
open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (tau : ℝ) (m : ℕ) :
    (∏ s : Fin 15,
      (componentBase tau s) ^
        (MME.DWZTable2Counts.component s * m)) =
      Real.rpow 2
        (componentLogRate tau *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) := by
  have hbase : ∀ s : Fin 15, 0 < componentBase tau s :=
    mme_dwz_square_componentBase_pos tau
  have hleft : 0 <
      (∏ s : Fin 15,
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m)) := by
    exact Finset.prod_pos fun s _ ↦ pow_pos (hbase s) _
  have hright : 0 <
      Real.rpow 2
        (componentLogRate tau *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  suffices hlog :
      Real.log
          (∏ s : Fin 15,
            (componentBase tau s) ^
              (MME.DWZTable2Counts.component s * m)) =
        Real.log
          (Real.rpow 2
            (componentLogRate tau *
              ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ))) by
    calc
      (∏ s : Fin 15,
          (componentBase tau s) ^
            (MME.DWZTable2Counts.component s * m)) =
          Real.exp (Real.log
            (∏ s : Fin 15,
              (componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m))) :=
        (Real.exp_log hleft).symm
      _ = Real.exp (Real.log
            (Real.rpow 2
              (componentLogRate tau *
                ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)))) := by
        rw [hlog]
      _ = Real.rpow 2
            (componentLogRate tau *
              ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) :=
        Real.exp_log hright
  rw [Real.log_prod]
  · simp_rw [Real.log_pow]
    change _ = Real.log ((2 : ℝ) ^
      (componentLogRate tau *
        ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)))
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    rw [componentLogRate]
    obtain ⟨hcomponent, _⟩ := mme_dwz_table2_integer_counts_exact
    have hscale : (0 : ℝ) < MME.DWZTable2Counts.scale := by
      norm_num [MME.DWZTable2Counts.scale]
    push_cast
    simp_rw [show ∀ s : Fin 15,
        (MME.DWZTable2Counts.component s : ℝ) =
          (MME.DWZTable2Counts.scale : ℝ) * alpha s by
      intro s
      exact (hcomponent s).symm]
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    rw [show
      (∑ s : Fin 15,
          alpha s * (Real.log (componentBase tau s) / Real.log 2)) *
            ((MME.DWZTable2Counts.scale : ℝ) * m) * Real.log 2 =
        ((MME.DWZTable2Counts.scale : ℝ) * m * Real.log 2) *
          (∑ s : Fin 15,
            alpha s * (Real.log (componentBase tau s) / Real.log 2)) by
      ring]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    field_simp [hlog2, ne_of_gt hscale]
  · intro s _
    exact pow_ne_zero _ (ne_of_gt (hbase s))
