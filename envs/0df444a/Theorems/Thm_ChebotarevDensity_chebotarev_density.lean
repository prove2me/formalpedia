-- Prove2me | Theorems.Thm_ChebotarevDensity_chebotarev_density
-- name    : ChebotarevDensity.chebotarev_density
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T17:17:12.270439+00:00
-- url     : https://prove2.me/theorems/4caa4c5f-8c1f-41bb-8676-343b70488178
-- title:
--   Chebotarëv's density theorem
-- statement:
--   Let $f$ be a polynomial with integer coefficients and leading coefficient $1$, and assume that its discriminant $\Delta(f)$ does not vanish. Let $K$ be the splitting field of $f$ over $\mathbb Q$, $G=\mathrm{Gal}(K/\mathbb Q)$ the Galois group of $f$, and let $C$ be a conjugacy class of $G$. Then the set of primes $p$ not dividing $\Delta(f)$ whose Frobenius substitution $\sigma_p$ belongs to $C$ has analytic (Dirichlet) density
--   $$\frac{\#C}{\#G}.$$
--
--   Here $\sigma\in G$ is a Frobenius substitution of $p$ if $\sigma(x)\equiv x^p\pmod{\mathfrak Q}$ for all algebraic integers $x\in\mathcal O_K$, for some prime ideal $\mathfrak Q$ of $\mathcal O_K$ above $p$; for $p\nmid\Delta(f)$ these elements form one conjugacy class, so "$\sigma_p\in C$" is unambiguous. The theorem is the common generalization of Dirichlet's theorem on primes in arithmetic progressions ($f=X^m-1$) and of Frobenius's theorem on decomposition types.
--
--   **Formalization Note** "$\sigma_p\in C$" is encoded as "some Frobenius substitution of $p$ lies in $C$". Density is analytic density, as in the source.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 34, "Chebotarev's Density Theorem"

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem chebotarev_density (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (C : ConjClasses (GalGroup f)) :
    HasDirichletDensity (chebotarevSet f C)
      ((Nat.card C.carrier : ℝ) / Nat.card (GalGroup f)) := by sorry

end ChebotarevDensity
