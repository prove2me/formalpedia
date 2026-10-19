-- Prove2me | Theorems.Thm_DusartCert_run_4
-- name    : DusartCert.run_4
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:36:00.552594+00:00
-- url     : https://prove2.me/theorems/4353fe7c-7bf9-4228-a7fa-10290a30bcf1
-- title:
--   Dusart finite-range certificate, block 4
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 4 (definition `DusartCert.Gen.items4`) and maps the state
--
--   $$(627089, 6, 30932256325294171710, 295191304195099104, 627089)\ \longmapsto\ (783151, 14, 31236217629858793834, 295191521532773423, 783151),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_4

theorem DusartCert.run_4 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items4 (627089, 6, 30932256325294171710, 295191304195099104, 627089) =
    some (783151, 14, 31236217629858793834, 295191521532773423, 783151) := by sorry
