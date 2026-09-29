-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.iterCech_cols_exact_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8a7e4ac1-e7c3-5a49-b6e5-81c998875190
-- title:
--   Exactness of the columns of the iterated Čech complex
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $\pi\colon Z\to\operatorname{Spec}R$ a separated morphism, and let $N$ be an $\mathcal O_Z$-module. Write $F=$ `ofModules π N` for the presheaf of $R$-modules $U\mapsto\Gamma(N,U)$, with the $R$-action obtained from $\pi$ and with the restriction maps of $N$ as $R$-linear transition maps. Assume $F$ is quasi-coherent in the sense of `IsQuasicoherent`: for every affine open $U\subseteq Z$ and every $f\in\Gamma(Z,U)$, each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $\mathfrak A$ and $\mathfrak B$ be ordered open families of $Z$ (finite linearly ordered index types together with families of opens) such that every $\mathfrak A.U\,i\sqcap\mathfrak B.U\,j$ is affine open and the supremum of all these pairwise intersections is $\top$, and let $\mathfrak C$ be an ordered affine cover of $Z$ (a finite linearly ordered family of affine opens with supremum $\top$) refining $\mathfrak B$, in the sense that each $\mathfrak C.U\,k$ lies in some $\mathfrak B.U\,j$. Then, for the iterated Čech double complex of $F$ attached to $\mathfrak A$, $\mathfrak B$ and $\mathfrak C$, each column is exact in the following three senses: for every $r$ the augmentation map `augCech`, which sends a Čech $r$-cochain $x$ for $\mathfrak C$ to the family whose value at a chain $K$ and a pair of multi-indices $st$ is the restriction of $x_K$ to $\mathfrak A.\mathrm{inter}\,st.1\sqcap(\mathfrak B\sqcap\mathfrak C.\mathrm{inter}\,K).\mathrm{inter}\,st.2$, is injective; for every $r$ the kernel of the vertical differential `dV` in degree $(r,0)$ equals the range of this augmentation; and for all $r$ and $m$ the kernel of `dV` in degree $(r,m+1)$ is contained in the range of `dV` in degree $(r,m)$ (an inclusion, the reverse one being part of the complex property).
--
--   This is the affine acyclicity input for the iterated (bi-)Čech construction: for each fixed $\mathfrak C$-chain the column is the total complex of the bi-Čech complex of $F$ for $\mathfrak A$ and the restriction of $\mathfrak B$ to that chain, and its exactness is the vanishing of higher Čech cohomology of a quasi-coherent sheaf on an affine scheme. It is used by [`AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent`](thm.html#AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent) and [`AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned) to compare the total cohomology of the bi-Čech complex with Čech cohomology of a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_IterCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.iterCech_cols_exact_of_isQuasicoherent
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : Z.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤)
    (ℭ : Z.OrderedAffineCover) (hrefine : ∀ k, ∃ j, ℭ.U k ≤ 𝔅.U j) :
    (∀ r, Function.Injective
        (OModulePresheaf.IterCech.augCech (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ r)) ∧
      (∀ r, LinearMap.ker (OModulePresheaf.IterCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily r 0)
        = LinearMap.range (OModulePresheaf.IterCech.augCech (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ r)) ∧
      ∀ r m, LinearMap.ker (OModulePresheaf.IterCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily r (m + 1))
        ≤ LinearMap.range (OModulePresheaf.IterCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily r m) := by sorry
