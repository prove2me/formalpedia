-- Prove2me | Theorems.Thm_DusartCert_run_22
-- name    : DusartCert.run_22
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:35:53.284392+00:00
-- url     : https://prove2.me/theorems/0e50d68e-bc44-4354-b141-26d2be0fe5cf
-- title:
--   Dusart finite-range certificate, block 22
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 22 (definition `DusartCert.Gen.items22`) and maps the state
--
--   $$(3352361, 29, 33113334439453082791, 295192160734121521, 3352361)\ \longmapsto\ (3499757, 24, 33165865565823600403, 295192168403659644, 3499757),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_22

theorem DusartCert.run_22 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items22 (3352361, 29, 33113334439453082791, 295192160734121521, 3352361) =
    some (3499757, 24, 33165865565823600403, 295192168403659644, 3499757) := by sorry
