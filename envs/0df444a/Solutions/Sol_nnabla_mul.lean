-- Prove2me | solution 1 for nnabla_mul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:37.386067+00:00
-- url     : https://prove2.me/submissions/68861082-ecfc-4040-aea9-ec1dc4db0aeb

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

set_option autoImplicit true

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}
omit [Sub α]

theorem solution [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  funext n
  simp [nnabla, smul_eq_mul, mul_sub]
