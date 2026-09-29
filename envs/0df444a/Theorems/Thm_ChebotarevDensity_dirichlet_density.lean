-- Prove2me | Theorems.Thm_ChebotarevDensity_dirichlet_density
-- name    : ChebotarevDensity.dirichlet_density
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T17:03:08.342524+00:00
-- url     : https://prove2.me/theorems/328ebb8c-252c-4d53-9eb2-cb7ca63fdaed
-- title:
--   Theorem of Dirichlet (analytic density of primes in arithmetic progressions)
-- statement:
--   Let $m$ be a positive integer and $a$ an integer with $\gcd(a,m)=1$. Then the set of primes $p$ with $p\equiv a\pmod m$ has analytic (Dirichlet) density $1/\varphi(m)$:
--   $$\lim_{s\to1^+}\frac{\sum_{p\equiv a\ (m)}p^{-s}}{\log\frac1{s-1}}=\frac1{\varphi(m)},$$
--   where $\varphi$ is Euler's totient function.
--
--   This is the case $f=X^m-1$ of Chebotarëv's theorem and the base case (cyclotomic extensions of $\mathbb Q$) of Chebotarëv's proof.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, pp. 30–31, "Theorem of Dirichlet" (with the definition of density given there)

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem dirichlet_density (m : ℕ) (hm : 0 < m) (a : ℤ) (ha : Int.gcd a m = 1) :
    HasDirichletDensity {p : ℕ | (p : ℤ) ≡ a [ZMOD m]} (1 / (Nat.totient m : ℝ)) := by sorry

end ChebotarevDensity
