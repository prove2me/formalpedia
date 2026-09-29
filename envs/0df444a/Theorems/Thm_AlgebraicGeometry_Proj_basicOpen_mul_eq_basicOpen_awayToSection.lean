-- Prove2me | Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
-- name    : AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1d6ffa08-e45c-5eb4-a8a2-a7f413b78ab9
-- title:
--   D₊(fg) as a basic open inside D₊(f)
-- statement:
--   Let $A$ be a commutative ring graded by $\mathbb N$ through a family $\mathcal A : \mathbb N \to \sigma$ of additive subgroups (a `GradedRing` structure), let $f, g \in A$ be homogeneous, $f \in \mathcal A_m$ and $g \in \mathcal A_{m'}$, with $m > 0$ and $m' > 0$. Write $V = D_+(f) =$ `Proj.basicOpen 𝒜 f` for the standard basic open of $\operatorname{Proj} \mathcal A$ attached to $f$, and let $e \in (A_f)_0 =$ `HomogeneousLocalization.Away 𝒜 f` be the degree-zero homogeneous fraction $g^{m}/f^{m'}$ produced by `HomogeneousLocalization.Away.isLocalizationElem` from the two degree witnesses. Let $s =$ `Proj.awayToSection 𝒜 f e` be the image of $e$ under the canonical map $(A_f)_0 \to \Gamma(\operatorname{Proj}\mathcal A, D_+(f))$. The assertion is an equality of opens of the scheme $\operatorname{Proj} \mathcal A$: the basic open $D_+(fg)$ attached to the homogeneous element $fg$ coincides with the scheme-theoretic basic open $(\operatorname{Proj}\mathcal A).\mathrm{basicOpen}\, s$, i.e. with the set of points of $D_+(f)$ at which the section $s$ has invertible image in the local ring.
--
--   This is the standard comparison between the basic opens $D_+(fg) \subseteq D_+(f)$ of $\operatorname{Proj}$ and the non-vanishing locus of the degree-zero ratio $g^{m}/f^{m'}$ read as a section of the structure sheaf; combined with the compatibility of basic opens with pullback it computes preimages $t^{-1}D_+(fg)$ of standard opens along a morphism $t : X \to \operatorname{Proj}\mathcal A$, for instance the locus inside $t^{-1}D_+(x_i)$ where a pulled-back coordinate ratio $x_k/x_i$ is invertible. It is used in the study of morphisms to $\operatorname{Proj}$ of a graded algebra, in results such as [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_mul_eq_zero_of_map_eq_zero`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_mul_eq_zero_of_map_eq_zero) and [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_eq_zero_of_preimage_basicOpen_eq_bot`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_eq_zero_of_preimage_basicOpen_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f g : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.basicOpen 𝒜 (f * g) =
      (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg)) := by sorry
