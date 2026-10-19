-- Prove2me | Theorems.Thm_DusartCert_run_19
-- name    : DusartCert.run_19
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:13.394827+00:00
-- url     : https://prove2.me/theorems/8982650d-9720-403b-99ca-56c5580f98af
-- title:
--   Dusart finite-range certificate, block 19
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 19 (definition `DusartCert.Gen.items19`) and maps the state
--
--   $$(2896253, 32, 32932796737298880252, 295192131736596007, 2896253)\ \longmapsto\ (3050233, 44, 32996692933121375127, 295192142487132653, 3050233),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_19

theorem DusartCert.run_19 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items19 (2896253, 32, 32932796737298880252, 295192131736596007, 2896253) =
    some (3050233, 44, 32996692933121375127, 295192142487132653, 3050233) := by sorry
