-- Prove2me | Theorems.Thm_ChebotarevDensity_hasDirichletDensity_primes
-- name    : ChebotarevDensity.hasDirichletDensity_primes
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T13:33:31.520836+00:00
-- url     : https://prove2.me/theorems/ecfe4015-28e2-424f-8291-aa37b4906779
-- title:
--   The set of all primes has Dirichlet density 1
-- statement:
--   The set of all primes has analytic (Dirichlet) density $1$:
--
--   $$\lim_{s\downarrow 1}\ \frac{\sum_{p\ \text{prime}} p^{-s}}{\log\frac{1}{s-1}} = 1 .$$
--
--   Equivalently, $\sum_p p^{-s} = \log\frac{1}{s-1}+O(1)$ as $s\downarrow 1$. This is the normalization against which the density of any set of primes is measured, and it is the first step in the analytic proofs of Dirichlet's theorem and of Chebotarëv's density theorem.
--
--   **Formalization Note** The sum is a `tsum` over the subtype of primes in the set, and the limit is taken within $(1,\infty)$, as in the definition `HasDirichletDensity`.
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, p. 31 (definition of analytic density); the asymptotic Σ_p p^{-s} ~ log 1/(s-1) follows from the Euler product of ζ and the simple pole of ζ at s=1 (e.g. Serre, A Course in Arithmetic, Ch. VI §3)

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem hasDirichletDensity_primes : HasDirichletDensity {p : ℕ | p.Prime} 1 := by sorry

end ChebotarevDensity
