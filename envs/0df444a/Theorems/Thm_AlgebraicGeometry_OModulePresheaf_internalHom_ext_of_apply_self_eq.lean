-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
-- name    : AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/aef8798a-2d1f-58fb-8d80-b1a822fea4a4
-- title:
--   Sections of the internal Hom over an affine open are determined at U
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, $\pi : V \to \operatorname{Spec} R$ a morphism, and let $F$ and $G$ be module data on the opens of $V$ over $\pi$ (to each open $U$ an $R$-module and $\Gamma(V,U)$-module $F(U)$, with compatible $R$-linear restriction maps semilinear over the restriction of functions). Assume $F$ and $G$ are quasi-coherent in the elementwise sense: for every affine open $U$ and every $f \in \Gamma(V,U)$, each section over the basic open $V_f$ becomes, after multiplication by the image of some power $f^n$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $V_f$ is killed by some $f^n$. Let $U$ be an affine open of $V$ and let $\varphi, \psi$ be two elements of the internal Hom of $F$ and $G$ at $U$, that is, two families assigning to every affine open $W \subseteq U$ a linear map $F(W) \to G(W)$, each family satisfying $\varphi_W(a \cdot x) = a \cdot \varphi_W(x)$ for $a \in \Gamma(V,W)$ and commuting with restriction along inclusions $W \subseteq W'$ of affine opens below $U$. If $\varphi_U(x) = \psi_U(x)$ for all $x \in F(U)$, then $\varphi = \psi$, i.e. all their components agree.
--
--   This is the uniqueness half of the identification, over an affine open $U$, of the sections of $\mathcal{H}om(\mathcal F,\mathcal G)$ with the $\Gamma(V,U)$-linear maps $\mathcal F(U) \to \mathcal G(U)$ for quasi-coherent data. It is cited in the proof of [`AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x) : φ = ψ := by sorry
