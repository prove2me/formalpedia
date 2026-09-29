-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/7f5b6398-b723-5805-af2f-9e54fea1f063
-- title:
--   Acyclicity of the mixed bi-Čech complex on U∩ V
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec} R$ a separated morphism, and let $N$ be a module over the structure sheaf of $X$. Write $F=$ `OModulePresheaf.ofModules π N` for the associated presheaf of $R$-modules on the opens of $X$, with $F(U)=\Gamma(N,U)$ and the restriction maps of $N$, and assume $F$ is quasi-coherent in the sense of the predicate `IsQuasicoherent`: for every affine open $U$ of $X$ and every $f\in\Gamma(X,U)$, each section over the basic open $D(f)$ becomes, after multiplication by some power $f^{n}$, the restriction of a section over $U$, and each section over $U$ whose restriction to $D(f)$ vanishes is annihilated by some $f^{n}$. Let $U,V$ be opens of $X$, let $\mathfrak V$ and $\mathfrak U$ be ordered affine covers of the open subschemes $V$ and $U$ (finite linearly ordered index sets together with affine opens covering the whole space), and let $\mathfrak W$ be such a cover of $U\sqcap V$. Assume, for the presheaf `ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)` attached to the restriction of $N$ to $U\sqcap V$, that the degree-zero alternating Čech group with respect to $\mathfrak W$ — the kernel of the Čech differential in degree $0$ — is the zero submodule, and that for every $i$ the quotient $\ker d^{i+1}/\operatorname{im} d^{i}$ is a subsingleton. Then for every $n$ the total cohomology in degree $n$ of the bounded double complex $F$.`biCech` formed from the two families of opens of $X$ obtained by pushing $\mathfrak V$ and $\mathfrak U$ forward along the open immersions $V.\iota$ and $U.\iota$ is a subsingleton; that is, $\ker d_{\mathrm{Tot}}^{\,0}=0$ and, for $n\ge 1$, $\ker d_{\mathrm{Tot}}^{\,n}$ coincides with the image of $d_{\mathrm{Tot}}^{\,n-1}$.
--
--   This is the $U\cap V$ term of Mayer–Vietoris for alternating Čech cohomology of a quasi-coherent module on a separated scheme: the mixed part of the Čech complex of the combined cover $\mathfrak V\sqcup\mathfrak U$ computes the cohomology of $U\cap V$, so it is acyclic as soon as that cohomology vanishes. It feeds the inductive step [`AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top), which propagates vanishing of higher Čech cohomology from two opens to their union.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent) (U V : X.Opens)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)
    (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover)
    (hW : (OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).H0 𝔚 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).HSucc 𝔚 i))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot
      ((OModulePresheaf.ofModules π N).biCech (𝔙.imageFamily V.ι) (𝔘.imageFamily U.ι)) n) := by sorry
