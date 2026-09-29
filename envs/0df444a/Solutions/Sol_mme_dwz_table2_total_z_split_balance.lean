-- Prove2me | solution 1 for mme_dwz_table2_total_z_split_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:46:07.344873+00:00
-- url     : https://prove2.me/submissions/92f5b70e-c586-4adf-8b40-43763fd99cdf

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open BigOperators
open MME MME.DWZStep1Histogram

set_option autoImplicit false
set_option warningAsError true

theorem solution (k : Fin 5) (a : Fin 3) :
    (∑ s : BoundaryComponentAt k, MME.DWZTable2Counts.split s.1 a) +
      MME.DWZTable2Counts.plusSplit k a = table2TotalZSplit k a := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun s : Fin 15 =>
      (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
        MME.DWZSquare.shapeZ s = k)) (by simp)
    (fun s => MME.DWZTable2Counts.split s a)]
  fin_cases k <;> fin_cases a <;> decide
