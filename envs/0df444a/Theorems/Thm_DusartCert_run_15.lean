-- Prove2me | Theorems.Thm_DusartCert_run_15
-- name    : DusartCert.run_15
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:23.77636+00:00
-- url     : https://prove2.me/theorems/0492c6c5-d961-4c66-bb3a-7f92463c836d
-- title:
--   Dusart finite-range certificate, block 15
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 15 (definition `DusartCert.Gen.items15`) and maps the state
--
--   $$(2297887, 15, 32643817001525632203, 295192075592042504, 2297887)\ \longmapsto\ (2440561, 34, 32719116165820546986, 295192091493095978, 2440561),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_15

theorem DusartCert.run_15 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items15 (2297887, 15, 32643817001525632203, 295192075592042504, 2297887) =
    some (2440561, 34, 32719116165820546986, 295192091493095978, 2440561) := by sorry
