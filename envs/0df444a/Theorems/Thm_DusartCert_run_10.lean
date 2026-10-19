-- Prove2me | Theorems.Thm_DusartCert_run_10
-- name    : DusartCert.run_10
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:09.858977+00:00
-- url     : https://prove2.me/theorems/74374d5d-c3ee-4b77-8686-4e742246c2d5
-- title:
--   Dusart finite-range certificate, block 10
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 10 (definition `DusartCert.Gen.items10`) and maps the state
--
--   $$(1543631, 29, 32135949121031599169, 295191939756728298, 1543631)\ \longmapsto\ (1691531, 43, 32253792558277808371, 295191976234856912, 1691531),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_10

theorem DusartCert.run_10 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items10 (1543631, 29, 32135949121031599169, 295191939756728298, 1543631) =
    some (1691531, 43, 32253792558277808371, 295191976234856912, 1691531) := by sorry
