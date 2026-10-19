-- Prove2me | Theorems.Thm_DusartCert_run_8
-- name    : DusartCert.run_8
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:36:00.758712+00:00
-- url     : https://prove2.me/theorems/d512f386-e00b-40de-99ef-29223cfa7bc1
-- title:
--   Dusart finite-range certificate, block 8
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 8 (definition `DusartCert.Gen.items8`) and maps the state
--
--   $$(1239877, 8, 31850028783494702718, 295191836174878117, 1239877)\ \longmapsto\ (1389643, 17, 31999319086394615890, 295191893083160260, 1389643),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_8

theorem DusartCert.run_8 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items8 (1239877, 8, 31850028783494702718, 295191836174878117, 1239877) =
    some (1389643, 17, 31999319086394615890, 295191893083160260, 1389643) := by sorry
