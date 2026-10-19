-- Prove2me | Theorems.Thm_DusartCert_run_12
-- name    : DusartCert.run_12
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:36:11.045462+00:00
-- url     : https://prove2.me/theorems/b1aa3f39-7467-40f4-a738-8f2eebb4fc26
-- title:
--   Dusart finite-range certificate, block 12
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 12 (definition `DusartCert.Gen.items12`) and maps the state
--
--   $$(1841113, 10, 32362236360802966132, 295192006970924857, 1841113)\ \longmapsto\ (1998221, 16, 32467007187711904599, 295192034295167718, 1998221),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_12

theorem DusartCert.run_12 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items12 (1841113, 10, 32362236360802966132, 295192006970924857, 1841113) =
    some (1998221, 16, 32467007187711904599, 295192034295167718, 1998221) := by sorry
