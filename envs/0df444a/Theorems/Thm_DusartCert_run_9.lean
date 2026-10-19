-- Prove2me | Theorems.Thm_DusartCert_run_9
-- name    : DusartCert.run_9
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:36:13.639876+00:00
-- url     : https://prove2.me/theorems/1deeca15-2eef-414d-9ef2-cf4c74eed591
-- title:
--   Dusart finite-range certificate, block 9
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 9 (definition `DusartCert.Gen.items9`) and maps the state
--
--   $$(1389643, 17, 31999319086394615890, 295191893083160260, 1389643)\ \longmapsto\ (1543631, 29, 32135949121031599169, 295191939756728298, 1543631),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_9

theorem DusartCert.run_9 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items9 (1389643, 17, 31999319086394615890, 295191893083160260, 1389643) =
    some (1543631, 29, 32135949121031599169, 295191939756728298, 1543631) := by sorry
