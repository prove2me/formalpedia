-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:50:42.903705+00:00
-- url     : https://prove2.me/submissions/fc93f1e8-e02d-414f-88d5-31cecf89f360

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_injective

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CWQ6Type2CyclicEdge N L G) (i : Fin 3)
    (hne : cwQ6Type2CyclicModeWord e i ≠
      cwQ6Type2CyclicModeWord f i) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord e i) r j -
        cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord f i) r j ≠ 0 := by
  have hcode :
      cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord e i) ≠
        cwQ6Type2CyclicHashModeCode p N i
          (cwQ6Type2CyclicModeWord f i) := by
    intro h
    exact hne (mme_CW_q6_type2_cyclic_hash_mode_code_injective hp i h)
  by_contra h
  push Not at h
  apply hcode
  funext r j
  exact sub_eq_zero.mp (h r j)
