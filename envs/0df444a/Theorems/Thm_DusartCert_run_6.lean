-- Prove2me | Theorems.Thm_DusartCert_run_6
-- name    : DusartCert.run_6
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:36:09.545165+00:00
-- url     : https://prove2.me/theorems/67f901e6-5033-4bf1-9a9c-d2b32824d2ee
-- title:
--   Dusart finite-range certificate, block 6
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 6 (definition `DusartCert.Gen.items6`) and maps the state
--
--   $$(938879, 40, 31481351364166126527, 295191664710676337, 938879)\ \longmapsto\ (1089523, 10, 31678971880380322602, 295191762507451599, 1089523),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_6

theorem DusartCert.run_6 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items6 (938879, 40, 31481351364166126527, 295191664710676337, 938879) =
    some (1089523, 10, 31678971880380322602, 295191762507451599, 1089523) := by sorry
