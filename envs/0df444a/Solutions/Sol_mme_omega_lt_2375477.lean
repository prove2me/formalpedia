-- Prove2me | solution 1 for mme_omega_lt_2375477
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:21:05.083878+00:00
-- url     : https://prove2.me/submissions/a5d5554e-a094-4df3-85d3-21ba2a2fca67

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_2375477

open MME

universe u

/-- Platform-ready proof matching the final printed-endpoint mission. -/
theorem solution {K : Type u} [Field K] :
    matMulExp K < 2375477 / 1000000 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt_2375477
