-- Prove2me | Theorems.Thm_FamousTheorems_dirichlet_primes_in_AP
-- name    : FamousTheorems.dirichlet_primes_in_AP
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:37.37341+00:00
-- url     : https://prove2.me/theorems/414ab4d4-e01a-4cad-a51a-dbd13c074efb
-- title:
--   Dirichlet's theorem on primes in arithmetic progressions
-- statement:
--   **Every admissible arithmetic progression contains infinitely many primes.**
--
--   For $\gcd(a,q) = 1$ there are infinitely many primes $p \equiv a \pmod q$.
--
--   The coprimality hypothesis is necessary: if $d = \gcd(a,q) > 1$ then every term of the
--   progression is divisible by $d$, so at most one is prime. The theorem says this is the only
--   obstruction — primes are distributed across **all** $\varphi(q)$ admissible residue classes.
--
--   Proved by Dirichlet in 1837, and the founding work of analytic number theory. He introduced
--   characters mod $q$ and their $L$-functions precisely to isolate a single residue class by
--   orthogonality, and the crux is that $L(1,\chi) \ne 0$ for every non-principal $\chi$ — without
--   which the primes could conspire to avoid a class. No elementary proof of the general case is
--   known.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dirichlet_primes_in_AP : ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by sorry

end FamousTheorems
