-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/15eb12c2-e957-5067-b581-97f3278d96f6
-- title:
--   Constancy of φ∘ P on a dual-number point
-- statement:
--   Let $k$ be a field, $X$ a scheme, $f : X \to \operatorname{Spec} k$ a morphism, $\mathcal{N}$ a sheaf of modules on $X$, $N$ a natural number, and let $\mathfrak{P}$ be a `ProjPresentation` of $\mathcal{N}$ over $f$ of size $N$: that is, global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal{N}$ together with a morphism $\varphi = \mathfrak{P}.toProj : X \to \operatorname{Proj}$ of the ring of homogeneous polynomials in $N+1$ variables over $k$ (projective $N$-space) satisfying $\varphi$ followed by the projection to $\operatorname{Spec} k$ equals $f$, the condition that over any open $V$ contained in $\varphi^{-1}(D_+(X_i))$ the map $g \mapsto g\cdot\sigma_i|_V$ is a bijection $\Gamma(X,V) \to \Gamma(\mathcal{N},V)$, and the relation $\varphi^\sharp(X_j/X_i)\cdot\sigma_i = \sigma_j$ on $\varphi^{-1}(D_+(X_i))$. Let $P : \operatorname{Spec} k[\varepsilon] \to X$ be a morphism from the dual numbers with $P$ followed by $f$ the structure morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$, and write $a$ for the composite of $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$ with $P$. Assume that for every global section $s : \mathbf{1} \to \mathcal{N}$, vanishing of the pulled-back section along $a$ implies vanishing of the pulled-back section along $P$ (pullback of a section being the canonical unit isomorphism composed with the image of $s$ under the pullback functor). Then $P$ followed by $\varphi$ equals the structure morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ followed by $a$ followed by $\varphi$.
--
--   This says that a tangent vector $P$ of $X$ which is annihilated by every global section of $\mathcal{N}$ vanishing at its base point is mapped by the morphism to projective space attached to the presentation to the constant tangent vector at $\varphi(a)$; equivalently, all affine coordinates of $\varphi\circ P$ in a chart containing the base point are constants in $k \subset k[\varepsilon]$. It is used in the injectivity arguments for morphisms to projective space defined by a polarisation, in the development of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp.lean

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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N)
    (P : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hincl : ∀ s : 𝟙_ X.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) s = 0 →
        Scheme.Modules.pullbackSection P s = 0) :
    P ≫ 𝔓.toProj = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
      ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) ≫ 𝔓.toProj) := by sorry
