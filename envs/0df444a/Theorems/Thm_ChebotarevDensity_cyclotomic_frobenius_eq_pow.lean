-- Prove2me | Theorems.Thm_ChebotarevDensity_cyclotomic_frobenius_eq_pow
-- name    : ChebotarevDensity.cyclotomic_frobenius_eq_pow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:16:23.847087+00:00
-- url     : https://prove2.me/theorems/4bbbda02-b545-4149-ae22-bfe1eeb1b1b6
-- title:
--   Frobenius substitution in cyclotomic fields: σ_p(ζ) = ζ^p
-- statement:
--   Let $m$ be a positive integer, let $K$ be the splitting field of $X^m-1$ over $\mathbb Q$ (the $m$-th cyclotomic field) and $G$ its Galois group. Let $p$ be a prime not dividing $m$, and let $\sigma\in G$ be a Frobenius substitution of $p$. Then for every primitive $m$-th root of unity $\zeta\in K$,
--   $$\sigma(\zeta)=\zeta^p .$$
--   In other words, under the isomorphism $G\cong(\mathbb Z/m\mathbb Z)^\times$, the Frobenius substitution $\sigma_p$ is a well-defined element (not just a conjugacy class) and corresponds to $p \bmod m$.
--
--   This identifies Dirichlet's theorem with the case $f=X^m-1$ of Chebotarëv's theorem.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 34: "if p is a prime number not dividing m, then the Frobenius substitution σ_p is the element of G that under the isomorphism G ≅ (Z/mZ)^* corresponds to (p mod m)"

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem cyclotomic_frobenius_eq_pow (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (σ : GalGroup (X ^ m - 1)) (hσ : IsFrobeniusAt (X ^ m - 1) p σ)
    (ζ : SplitField (X ^ m - 1)) (hζ : IsPrimitiveRoot ζ m) :
    σ ζ = ζ ^ p := by sorry

end ChebotarevDensity
