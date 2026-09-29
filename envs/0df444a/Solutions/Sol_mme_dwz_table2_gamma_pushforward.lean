-- Prove2me | solution 1 for mme_dwz_table2_gamma_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:38:03.151813+00:00
-- url     : https://prove2.me/submissions/03a3b2b9-d472-4ea3-b6ba-4df1eeead675

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_pair_coarsening

open BigOperators Finset

set_option autoImplicit false

theorem solution (k : Fin 5) :
    (∑ p : {p : Fin 3 × Fin 3 //
        MME.DWZTable2Counts.coarseOf p = k},
      MME.DWZTable2Counts.gamma p.1) =
      MME.DWZTable2Counts.alphaZ k := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun p : Fin 3 × Fin 3 ↦
      MME.DWZTable2Counts.coarseOf p = k)) (by simp)]
  fin_cases k <;> rw [Finset.sum_filter, Fintype.sum_prod_type] <;>
    simp [MME.DWZTable2Counts.coarseOf,
      MME.DWZTable2Counts.gamma, MME.DWZTable2Counts.alphaZ,
      Fin.sum_univ_succ]
