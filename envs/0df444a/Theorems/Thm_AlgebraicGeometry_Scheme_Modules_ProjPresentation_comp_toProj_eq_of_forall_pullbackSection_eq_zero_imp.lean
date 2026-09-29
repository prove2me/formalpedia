-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/af22a172-c319-5d94-a0ad-664ef5de8361
-- title:
--   Two k-points with the same vanishing sections have equal images in P^N
-- statement:
--   Let $k$ be a field, $X$ a scheme, $f : X \to \operatorname{Spec} k$ a morphism, $\mathcal N$ a sheaf of modules on $X$, $N$ a natural number, and let $\mathfrak P$ be a `ProjPresentation` of $\mathcal N$ over $f$ of size $N$: that is, global sections $\sigma_i \in \Gamma(\mathcal N, \top)$ indexed by $i \in \mathrm{Fin}(N+1)$ together with a morphism $\mathfrak P.\mathtt{toProj} : X \to \operatorname{Proj}$ of the homogeneous-submodule grading of $k[x_0,\dots,x_N]$ (so $\mathbb{P}^N_k$) satisfying: composing $\mathfrak P.\mathtt{toProj}$ with the structure morphism $\pi$ of $\mathbb{P}^N_k$ gives $f$; for each $i$ and each open $V \le \mathfrak P.\mathtt{toProj}^{-1}D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(\mathcal N,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective; and on $\mathfrak P.\mathtt{toProj}^{-1}D_+(x_i)$ the pullback along $\mathfrak P.\mathtt{toProj}$ of the degree-zero fraction $x_j/x_i$ times $\sigma_i$ equals $\sigma_j$. Let $p, q : \operatorname{Spec} k \to X$ be sections of $f$, i.e. $p \circ f = \mathrm{id}$ and $q \circ f = \mathrm{id}$ in diagrammatic order. Assume that for every morphism $s$ from the unit module $\mathcal O_X$ to $\mathcal N$, vanishing of the pulled-back section along $p$ (the composite of the inverse of the canonical isomorphism $p^*\mathcal O_X \cong \mathcal O_{\operatorname{Spec} k}$ with $p^*s$) forces vanishing of the corresponding pulled-back section along $q$. Then $p$ followed by $\mathfrak P.\mathtt{toProj}$ equals $q$ followed by $\mathfrak P.\mathtt{toProj}$, i.e. $p$ and $q$ have the same image as $k$-points of $\mathbb{P}^N_k$.
--
--   This is the separation statement for a base-point-free system of global sections: the morphism to $\mathbb{P}^N$ determined by a presentation of $\mathcal N$ can only separate two $k$-points of $X$ when some global section of $\mathcal N$ vanishes at one and not the other. It is used in the treatment of polarisations, where it yields that two points with the same vanishing sections have proportional images, via [`AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero`](thm.html#AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_of_forall_pullbackSection_eq_zero_imp
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N)
    (p q : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (hincl : ∀ s : 𝟙_ X.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection p s = 0 → Scheme.Modules.pullbackSection q s = 0) :
    p ≫ 𝔓.toProj = q ≫ 𝔓.toProj := by sorry
