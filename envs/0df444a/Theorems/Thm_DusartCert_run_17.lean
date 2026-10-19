-- Prove2me | Theorems.Thm_DusartCert_run_17
-- name    : DusartCert.run_17
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:37:15.096232+00:00
-- url     : https://prove2.me/theorems/d852c8a4-b363-4830-a916-25a2e1f062a3
-- title:
--   Dusart finite-range certificate, block 17
-- statement:
--   The kernel checker `DusartCert.run` with $Q=2^{64}$ accepts certificate block 17 (definition `DusartCert.Gen.items17`) and maps the state
--
--   $$(2592589, 31, 32794939795817715799, 295192106567167876, 2592589)\ \longmapsto\ (2748587, 24, 32867759843802371053, 295192120209138332, 2731087),$$
--
--   where a state is (current wheel candidate $n$, wheel index, $Q$-scaled upper sum of $1/p$ over primes $11\le p<n$, $Q$-scaled upper sum of $-\log(1-1/p)-1/p$ over the same primes, left end of the next mesh cell). Every mesh cell closed inside the block passed its check.
--
--   This is one of 24 blocks of the kernel-checked finite range of Dusart's Theorem 6.10; the blocks chain, from the initial state $(11,1,0,0,10372)$ to $n=3594643$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Definitions.Def_DusartCertData_17

theorem DusartCert.run_17 :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items17 (2592589, 31, 32794939795817715799, 295192106567167876, 2592589) =
    some (2748587, 24, 32867759843802371053, 295192120209138332, 2731087) := by sorry
