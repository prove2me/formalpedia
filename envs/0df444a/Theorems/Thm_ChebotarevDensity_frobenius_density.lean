-- Prove2me | Theorems.Thm_ChebotarevDensity_frobenius_density
-- name    : ChebotarevDensity.frobenius_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:16:46.844406+00:00
-- url     : https://prove2.me/theorems/b9756187-4ae8-4978-8fec-0fab17438db6
-- title:
--   Theorem of Frobenius (density of primes with a given decomposition type)
-- statement:
--   Let $f\in\mathbb Z[X]$ be monic with discriminant $\Delta(f)\neq0$, and let $G$ be its Galois group, viewed as a group of permutations of the $n$ zeros of $f$. Let $t$ be a partition of $n$ (a multiset of positive integers). Then the set of primes $p\nmid\Delta(f)$ for which $f \bmod p$ has decomposition type $t$ has analytic density
--   $$\frac{\#\{\sigma\in G:\ \sigma\text{ has cycle pattern } t\}}{\#G}.$$
--
--   In particular the primes modulo which $f$ splits into linear factors have density $1/\#G$.
--
--   **Formalization Note** $t$ ranges over all multisets of natural numbers; if $t$ is not a partition of $n$ both the set and the count are empty and the density is $0$.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 33, "Theorem of Frobenius"

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem frobenius_density (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0) (t : Multiset ℕ) :
    HasDirichletDensity (decompositionTypeSet f t)
      ((Nat.card {σ : GalGroup f // cyclePattern f σ = t} : ℝ) / Nat.card (GalGroup f)) := by sorry

end ChebotarevDensity
