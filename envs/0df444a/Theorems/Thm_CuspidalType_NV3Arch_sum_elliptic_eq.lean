-- Prove2me | Theorems.Thm_CuspidalType_NV3Arch_sum_elliptic_eq
-- name    : CuspidalType.NV3Arch.sum_elliptic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/17d56c7e-b37b-5cf9-9c7d-218af71e842c
-- title:
--   Elliptic class sums versus non-split torus sums in GL₂
-- statement:
--   Fix a prime $q$ and write $\mathrm{GL}_2(\mathbb{F}_q)$ for `GL2 q`, the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$, and $\mathbb{F}_{q^2}$ for `GaloisField q 2`, whose unit group is taken to be finite. Let $K$ be a commutative ring and $F \colon \mathrm{GL}_2(\mathbb{F}_q) \to K$ a function invariant under conjugation, i.e. $F(hgh^{-1}) = F(g)$ for all $g, h$. Let $\mathrm{torus}\,q \colon \mathbb{F}_{q^2}^{\times} \to \mathrm{GL}_2(\mathbb{F}_q)$ be the monoid homomorphism sending a unit $\alpha$ to the matrix of multiplication by $\alpha$ on $\mathbb{F}_{q^2}$, computed in the fixed $\mathbb{Z}/q$-basis `quadBasis q` of $\mathbb{F}_{q^2}$ indexed by `Fin 2`. The assertion is the identity in $K$
--   $$2(q^2-1)\sum_{g} F(g) \;=\; \#\mathrm{GL}_2(\mathbb{F}_q) \cdot \sum_{\alpha} F(\mathrm{torus}\,q\,\alpha),$$
--   where the left-hand sum runs over those $g \in \mathrm{GL}_2(\mathbb{F}_q)$ whose characteristic polynomial has no root in $\mathbb{Z}/q$, the right-hand sum runs over those units $\alpha$ of $\mathbb{F}_{q^2}$ whose underlying element does not lie in the image of the structure map $\mathbb{Z}/q \to \mathbb{F}_{q^2}$, and the two scalars are the natural numbers $2(q^2-1)$ and $\#\mathrm{GL}_2(\mathbb{F}_q)$ cast into $K$. No division by $2(q^2-1)$ is performed, so $K$ need not be of characteristic coprime to it.
--
--   This is the standard two-to-one parametrisation of the elliptic (anisotropic regular semisimple) conjugacy classes of $\mathrm{GL}_2(\mathbb{F}_q)$ by the elements of the non-split torus $\mathbb{F}_{q^2}^{\times}$ not lying in $\mathbb{F}_q$, recorded as a division-free identity between sums of a class function. It is used in the computation of sums of characters over torus elements in [`CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv`](thm.html#CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv), part of the analysis of cuspidal types for $\mathrm{GL}_2(\mathbb{F}_q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_NV3Arch_sum_elliptic_eq.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial CuspidalType in
open scoped Classical in

theorem CuspidalType.NV3Arch.sum_elliptic_eq (q : ℕ) [Fact q.Prime]
    [Fintype (GaloisField q 2)ˣ] {K : Type*} [CommRing K] (F : GL2 q → K)
    (hF : ∀ g h : GL2 q, F (h * g * h⁻¹) = F g) :
    (2 * (q ^ 2 - 1 : ℕ) : K) *
        ∑ g ∈ Finset.univ.filter
          (fun g : GL2 q => ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x), F g =
      (Nat.card (GL2 q) : K) *
        ∑ α ∈ Finset.univ.filter
          (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
          F (torus q α) := by sorry
