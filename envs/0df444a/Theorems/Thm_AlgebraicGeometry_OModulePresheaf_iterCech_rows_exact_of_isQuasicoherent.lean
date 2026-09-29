-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_iterCech_rows_exact_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.iterCech_rows_exact_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/60b71037-88b2-5cdc-8a48-1e26a78217a8
-- title:
--   Exact augmented rows of the iterated Čech complex
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $\pi\colon Z\to\operatorname{Spec} R$ a separated morphism. Let $N$ be an $\mathcal{O}_Z$-module and let $F=$ `ofModules π N` be the associated presheaf of $R$-modules $U\mapsto\Gamma(N,U)$, with $R$ acting through $\pi$ and with restriction maps the module restrictions; assume $F$ is quasi-coherent in the sense of `IsQuasicoherent`: for every affine open $U\subseteq Z$ and every $f\in\Gamma(Z,U)$, each section over the basic open $Z_f$ becomes, after multiplication by the image of some power $f^n$, the restriction of a section over $U$, and each section over $U$ whose restriction to $Z_f$ vanishes is annihilated by some $f^n$. Let $\mathfrak{A},\mathfrak{B}$ be ordered open families of $Z$ (finite linearly ordered index sets together with families of opens) such that $\mathfrak{A}.U\,i\sqcap\mathfrak{B}.U\,j$ is affine open for all $i,j$, and let $\mathfrak{C}$ be an ordered affine cover of $Z$ (finite linearly ordered index set, affine opens with supremum $\top$), regarded as an open family. Write $\mathrm{Tot}^m$ for the total degree-$m$ term (the product over pairs $(p,q)$ with $p+q=m$) of the bounded double Čech complex `biCech` of $F$ for $\mathfrak{A},\mathfrak{B}$, and let $\varepsilon_m=$ `IterCech.augTot` be the map into `IterCech.C` in horizontal degree $0$ whose component at an index tuple $K$ of $\mathfrak{C}$ is restriction of all slots to $\mathfrak{C}.\mathrm{inter}\,K=\bigsqcap_j\mathfrak{C}.U\,K_j$. The theorem asserts three things: for each $m$, $\varepsilon_m$ is injective; for each $m$, the kernel of the horizontal differential `IterCech.dH` out of horizontal degree $0$ equals the image of $\varepsilon_m$; and for all $r,m$, the kernel of `IterCech.dH` out of horizontal degree $r+1$ is contained in the image of `IterCech.dH` out of horizontal degree $r$.
--
--   This is the slot-wise application of the vanishing of higher Čech cohomology of a quasi-coherent module on an affine scheme, here for the covers $(\mathfrak{A}_s\cap\mathfrak{B}_t\cap\mathfrak{C}_k)_k$ of the affine opens $\mathfrak{A}_s\cap\mathfrak{B}_t$: each row of the iterated Čech complex, augmented by restriction to the members of $\mathfrak{C}$, is exact. It is the input to the comparison of the total bi-Čech cohomology with that computed from a product cover, used by `exists_HTot_biCech_equiv_prodCover_cup_pinned` and `nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_iterCech_rows_exact_of_isQuasicoherent.lean

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

theorem AlgebraicGeometry.OModulePresheaf.iterCech_rows_exact_of_isQuasicoherent
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : Z.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (ℭ : Z.OrderedAffineCover) :
    (∀ m, Function.Injective
        (OModulePresheaf.IterCech.augTot (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily m)) ∧
      (∀ m, LinearMap.ker (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily 0 m)
        = LinearMap.range (OModulePresheaf.IterCech.augTot (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily m)) ∧
      ∀ r m, LinearMap.ker (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily (r + 1) m)
        ≤ LinearMap.range (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily r m) := by sorry
