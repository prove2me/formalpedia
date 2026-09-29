-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top
-- name    : AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8cdb0032-6306-5b77-af12-ef5b88f30381
-- title:
--   Čech vanishing on X and U∩ V descends to V
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec}R$ a separated morphism, and let $N$ be an $\mathcal O_X$-module whose presheaf of sections, viewed as the $R$-linear presheaf `OModulePresheaf.ofModules π N`, is quasi-coherent in the sense that for every affine open $U$ and every $f\in\Gamma(X,U)$ each section over the basic open $X_f$ becomes, after multiplication by some power $f^n$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $X_f$ is annihilated by some $f^n$. Let $U,V\subseteq X$ be opens with $U\sqcup V=\top$, and fix ordered affine covers — a finite linearly ordered index set together with affine opens whose supremum is the whole space — namely $\mathfrak X$ of $X$, $\mathfrak V$ of the open subscheme $V$ and $\mathfrak W$ of the open subscheme $U\cap V$. Assume that for $\mathfrak X$ and $N$ the kernel of the $0$-th alternating Čech differential is zero and every quotient $\ker d^{i+1}/\operatorname{im}d^{i}$ is trivial, and likewise for $\mathfrak W$ and the restriction of $N$ along $U\cap V\hookrightarrow X$ over the composite structure morphism. Then the same two conclusions hold for $\mathfrak V$ and the restriction of $N$ to $V$.
--
--   This is the excision, or Mayer–Vietoris, step for alternating Čech cohomology of a quasi-coherent module on a separated scheme with a two-open cover $X=U\cup V$: vanishing on $X$ and on $U\cap V$ forces vanishing on $V$. It is used in the study of line bundles with trivial class, in [`AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite`](thm.html#AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔙 : (V : Scheme.{u}).OrderedAffineCover)
    (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover)
    (hX : (OModulePresheaf.ofModules π N).H0 𝔛 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛 i))
    (hW : (OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).H0 𝔚 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).HSucc 𝔚 i)) :
    (OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).H0 𝔙 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).HSucc 𝔙 i) := by sorry
