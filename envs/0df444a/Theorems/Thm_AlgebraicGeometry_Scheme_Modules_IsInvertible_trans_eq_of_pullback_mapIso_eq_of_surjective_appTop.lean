-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/994d555a-8cdb-59ae-bed2-95d4eca2103a
-- title:
--   Rigidified isomorphisms of invertible modules compose
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme, let $f : A \to \operatorname{Spec} S$ be a morphism admitting a section $e : \operatorname{Spec} S \to A$, so that $e$ followed by $f$ is the identity, and assume the induced ring map on global sections, $f$`.appTop`, is surjective. Let $L_1, L_2, L_3$ be sheaves of modules on $A$, and assume $L_1$ satisfies `Scheme.Modules.IsInvertible`, i.e. every point of $A$ has an open neighbourhood $U$ for which the pullback of $L_1$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module (the structure sheaf) of $U$. Let $\rho_1, \rho_2, \rho_3$ be rigidifications, that is, isomorphisms $e^{*}L_a \cong \mathcal{O}_{\operatorname{Spec} S}$ in the category of modules over the structure sheaf of $\operatorname{Spec} S$. Let $\varphi_{12} : L_1 \cong L_2$, $\varphi_{23} : L_2 \cong L_3$ and $\varphi_{13} : L_1 \cong L_3$ be isomorphisms that are normalised along $e$ in the sense that $e^{*}\varphi_{ab}$ equals the composite of $\rho_a$ with $\rho_b^{-1}$ for $(a,b) = (1,2), (2,3), (1,3)$. Then $\varphi_{12}$ followed by $\varphi_{23}$ equals $\varphi_{13}$.
--
--   This is the transitivity (cocycle) compatibility for isomorphisms of invertible modules normalised against given rigidifications along a section, in the setting used to build the relative Picard functor of rigidified line bundles. It is used in the construction of the pullback isomorphisms satisfying the cocycle condition over a family of charts of a rigidified invertible module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ₀ : Function.Surjective (f.appTop).hom)
    (L₁ L₂ L₃ : A.Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (ρ₁ : (Scheme.Modules.pullback e).obj L₁ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (ρ₂ : (Scheme.Modules.pullback e).obj L₂ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (ρ₃ : (Scheme.Modules.pullback e).obj L₃ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (φ₁₂ : L₁ ≅ L₂) (φ₂₃ : L₂ ≅ L₃) (φ₁₃ : L₁ ≅ L₃)
    (h₁₂ : (Scheme.Modules.pullback e).mapIso φ₁₂ = ρ₁ ≪≫ ρ₂.symm)
    (h₂₃ : (Scheme.Modules.pullback e).mapIso φ₂₃ = ρ₂ ≪≫ ρ₃.symm)
    (h₁₃ : (Scheme.Modules.pullback e).mapIso φ₁₃ = ρ₁ ≪≫ ρ₃.symm) :
    φ₁₂ ≪≫ φ₂₃ = φ₁₃ := by sorry
