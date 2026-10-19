-- Prove2me | Theorems.Thm_DusartCert_run_21
-- name    : DusartCert.run_21
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:20.075381+00:00
-- url     : https://prove2.me/theorems/116ff17a-48ab-43e7-adf1-5985160a8c28
-- title:
--   Dusart finite-range certificate, block 21
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 21 (definition `DusartCert.Gen.items21`) and maps the state
--
--   $$(3206479, 46, 33058594441692615397, 295192152384528891, 3188987)\ \longmapsto\ (3352361, 29, 33113334439453082791, 295192160734121521, 3352361),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_21

theorem DusartCert.run_21 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items21 (3206479, 46, 33058594441692615397, 295192152384528891, 3188987) =
    some (3352361, 29, 33113334439453082791, 295192160734121521, 3352361) := by sorry
