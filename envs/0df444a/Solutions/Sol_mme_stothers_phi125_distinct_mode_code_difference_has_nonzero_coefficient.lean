-- Prove2me | solution 1 for mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:41:13.006728+00:00
-- url     : https://prove2.me/submissions/be52d641-d513-403d-9bf7-fdeceb63d8b1

import Theorems.Thm_mme_stothers_phi125_cyclic_hash_mode_code_injective

open MME.StothersFourth.Phi125

theorem solution {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (i : Fin 3) (u v : CyclicModeWord N) (huv : u ≠ v) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cyclicHashModeCode p N i u r j - cyclicHashModeCode p N i v r j ≠ 0 := by
  by_contra h
  push_neg at h
  apply huv
  apply mme_stothers_phi125_cyclic_hash_mode_code_injective hp i
  funext r j
  exact sub_eq_zero.mp (h r j)

#print axioms solution
