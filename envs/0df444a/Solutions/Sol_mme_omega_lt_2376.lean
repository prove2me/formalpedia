-- Prove2me | solution 1 for mme_omega_lt_2376
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:02:46.467814+00:00
-- url     : https://prove2.me/submissions/647177b7-8453-47cc-8232-ec2021775190

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_2376

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 297 / 125 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt_2376
