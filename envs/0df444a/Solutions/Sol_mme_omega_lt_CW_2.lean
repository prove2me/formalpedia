-- Prove2me | solution 2 for mme_omega_lt_CW
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T02:53:11.422712+00:00
-- url     : https://prove2.me/submissions/bf1bf861-e699-468a-a1c4-46b4ab1a866c

import Definitions.Def_mme_omega
import Theorems.Thm_mme_omega_lt_2376
open MME
set_option autoImplicit true

/-- The Coppersmith–Winograd bound `ω < 2.376`, obtained from the platform theorem
`mme_omega_lt_2376 : matMulExp K < 297 / 125` and the identity `2376 / 1000 = 297 / 125`. -/
theorem solution {K : Type u} [Field K] : matMulExp K < 2376 / 1000 := by
  have h : matMulExp K < 297 / 125 := mme_omega_lt_2376 (K := K)
  have heq : (2376 : ℝ) / 1000 = 297 / 125 := by norm_num
  rw [heq]
  exact h
