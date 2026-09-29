-- Prove2me | Theorems.Thm_Algebra_norm_eq_finprod_norm_quotient_pow_length
-- name    : Algebra.norm_eq_finprod_norm_quotient_pow_length
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4f35862d-bf3d-5baa-afc2-c56da47fbccd
-- title:
--   Norm as a product of residue norms weighted by local lengths
-- statement:
--   Let $K$ be a field and $A$ a commutative ring carrying a $K$-algebra structure which is finite as a $K$-module, and let $a \in A$. The assertion is an equality in $K$ between $\mathrm{N}_{A/K}(a)$, the determinant of multiplication by $a$ on $A$ viewed as a finite $K$-module, and the product, taken over the maximal spectrum of $A$ (the type of maximal ideals $\mathfrak m$ of $A$, the product being a `finprod`, i.e. a product over the finite support of the family), of the factors $\mathrm{N}_{(A/\mathfrak m)/K}(a \bmod \mathfrak m)^{e_{\mathfrak m}}$. Here $a \bmod \mathfrak m$ is the image of $a$ under the quotient map $A \to A/\mathfrak m$ and the norm is taken for the induced $K$-algebra structure on $A/\mathfrak m$, while the exponent $e_{\mathfrak m}$ is the natural number obtained from the length of the localisation $A_{\mathfrak m}$ as a module over itself, i.e. the length of the local ring $A_{\mathfrak m}$, converted from an extended natural number to $\mathbb N$. No reducedness, nontriviality or separability hypothesis is imposed on $A$.
--
--   This is the standard decomposition of the norm of a finite-dimensional commutative algebra over a field into local contributions, reflecting the splitting of the Artinian ring $A$ into the product of its localisations at its finitely many maximal ideals. It is used in the computation of norms of quotients by a principal ideal in the crossing-model computations for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_eq_finprod_norm_quotient_pow_length.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Algebra.norm_eq_finprod_norm_quotient_pow_length
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] (a : A) :
    Algebra.norm K a =
      ∏ᶠ 𝔪 : MaximalSpectrum A,
        Algebra.norm K (Ideal.Quotient.mk 𝔪.asIdeal a) ^
          (Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal)).toNat := by sorry
