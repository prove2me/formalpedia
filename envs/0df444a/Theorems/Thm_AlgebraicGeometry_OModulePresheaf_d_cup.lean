-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_cup
-- name    : AlgebraicGeometry.OModulePresheaf.d_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/18251c8c-7cd0-5504-bfe1-fe1970fec449
-- title:
--   Leibniz rule for the Čech cup product
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi \colon V \to \operatorname{Spec} R$. Let $F$ be an `OModulePresheaf` over $\pi$, that is: an assignment to each open $U \subseteq V$ of an abelian group $F.\mathrm{obj}(U)$ carrying an $R$-module and a $\Gamma(V,U)$-module structure which are compatible via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $F.\mathrm{res}$ for $U \le U'$ that are semilinear over the presheaf restriction $\Gamma(V,U') \to \Gamma(V,U)$, are the identity for $U = U'$ and compose functorially. Let $\mathcal{K}$ be an `OrderedAffineCover` of $V$: a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$. For $i \in \mathbb{N}$, an $i$-cochain of $F$ is a family assigning to each $s \in \mathcal{K}.\mathrm{Idx}\ i$ (a strictly increasing $i$-tuple of indices) an element of $F.\mathrm{obj}$ of the intersection $\bigwedge_j U_{s(j)}$. Let $a, b, n$ be natural numbers with $a + b = n$, let $\alpha$ be an $a$-cochain for `OModulePresheaf.unit π` (the presheaf $U \mapsto \Gamma(V,U)$ with its $\pi$-induced $R$-algebra structure and ring-map restrictions) and let $\beta$ be a $b$-cochain of $F$. Here $F.\mathrm{cup}$ is the product whose value at $s$ is the restriction of $\alpha$ at the front face of $s$ (its first $a$ entries) acting, through the $\Gamma$-module structure, on the restriction of $\beta$ at the back face of $s$ (its last $b$ entries), and $F.d$ denotes the differential raising cochain degree by one. The assertion is the identity of $(n+1)$-cochains $$F.d\,(\alpha \cup \beta) = (d\alpha) \cup \beta + (-1)^a \cdot \bigl(\alpha \cup d\beta\bigr),$$ the cup products on the right being taken in bidegrees $(a+1, b)$ and $(a, b+1)$ with total degree $n+1$, and $(-1)^a$ acting as an integer scalar.
--
--   This is the Leibniz (graded derivation) rule for the Čech cup product on cochains of an ordered affine cover, in the form where the left factor is a cochain of the structure presheaf and the right factor a cochain of an $\mathcal{O}$-module presheaf. It underlies the fact that the cup product of cocycles is a cocycle and that cupping with a coboundary yields a coboundary, and it is used in the construction of the graded-ring structure on Čech cohomology and in the comparison of bi-Čech with product-cover cup products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_cup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.d_cup
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) (a b n : ℕ) (h : a + b = n)
    (α : (OModulePresheaf.unit π).cochain 𝒦 a) (β : F.cochain 𝒦 b) :
    F.d 𝒦 n (F.cup 𝒦 a b n h α β) =
      F.cup 𝒦 (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).d 𝒦 a α) β +
        ((-1 : ℤ) ^ a) • F.cup 𝒦 a (b + 1) (n + 1) (by omega) α (F.d 𝒦 b β) := by sorry
