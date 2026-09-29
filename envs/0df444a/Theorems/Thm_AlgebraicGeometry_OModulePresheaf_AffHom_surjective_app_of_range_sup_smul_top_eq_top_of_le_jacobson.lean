-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
-- name    : AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/634ea421-2119-5346-8d52-778e88accbe6
-- title:
--   Nakayama surjectivity over a universally closed base
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal contained in the Jacobson radical $\mathrm{Jac}(R)$, formalised as $I \le (\bot : \mathrm{Ideal}\ R).\mathrm{jacobson}$, let $X$ be a scheme and let $f : X \to \operatorname{Spec} R$ be universally closed. Let $F$ and $G$ be presheaves of $\mathcal O_X$-modules in the project's sense (`OModulePresheaf f`): for each open $U$ of $X$ a type $F(U)$ carrying compatible $R$- and $\Gamma(X,U)$-module structures, with $R$-linear restriction maps that are semilinear for restriction of sections and functorial. Assume: $F$ is quasi-coherent, i.e. for every affine open $U$ and every $a \in \Gamma(X,U)$ each element of $F(D(a))$ becomes, after multiplication by some power $a^n$, the restriction of an element of $F(U)$, and every element of $F(U)$ restricting to $0$ on $D(a)$ is annihilated by some $a^n$; $G$ is coherent, i.e. $G(U)$ is a finite $\Gamma(X,U)$-module for every affine open $U$; and $G$ is quasi-coherent in the same elementwise sense. Let $\varphi$ be an `AffHom` from $F$ to $G$, that is, a family of $R$-linear maps $\varphi_U : F(U) \to G(U)$ indexed by the affine opens $U$, each compatible with multiplication by sections of $\Gamma(X,U)$ and commuting with restriction along inclusions of affine opens. Suppose that for every affine open $U$ of $X$ one has $\operatorname{range}(\varphi_U) + I \cdot G(U) = G(U)$ as $R$-submodules of $G(U)$. Then for every affine open $U$ the map $\varphi_U$ is surjective.
--
--   This is the globalisation over a universally closed base of Nakayama's lemma: surjectivity modulo an ideal in the Jacobson radical of the base ring, checked on all affine opens, implies genuine surjectivity on all affine opens; the classical form appears in EGA III₁ around Cor. 5.1.6. It is used in the construction of ideal sheaf data whose adic thickenings have prescribed pullbacks, in the adically complete, closed-immersion setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [UniversallyClosed f]
    {F G : OModulePresheaf f} (hF : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (φ : OModulePresheaf.AffHom F G)
    (h : ∀ U : X.affineOpens, LinearMap.range (φ.app U) ⊔ I • (⊤ : Submodule R (G.obj U.1)) = ⊤)
    (U : X.affineOpens) : Function.Surjective (φ.app U) := by sorry
