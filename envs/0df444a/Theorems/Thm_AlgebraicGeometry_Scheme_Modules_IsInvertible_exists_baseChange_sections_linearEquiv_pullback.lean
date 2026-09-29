-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/da9c50eb-5677-5ead-a9bb-cfa36ce53770
-- title:
--   Affine base change for sections of an invertible sheaf
-- statement:
--   Let $X$ and $Z$ be schemes, let $p \colon Z \to X$ be a morphism, and let $L$ be a sheaf of modules on $X$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \subseteq X$ with $x \in U$ such that the inverse image of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module (the structure sheaf as a module over itself) on $U$. Let $U$ be an open subset of $X$ which is affine, and assume that the preimage $p^{-1}(U)$ is an affine open of $Z$. Write $A = \Gamma(X, U)$ and $B = \Gamma(Z, p^{-1}(U))$, the latter regarded as an $A$-algebra through the ring homomorphism $\Gamma(X,U) \to \Gamma(Z, p^{-1}U)$ that $p$ induces on sections over $U$. Then there exists a $B$-linear isomorphism
--   $$\beta \colon B \otimes_{A} \Gamma(L, U) \;\xrightarrow{\ \sim\ }\; \Gamma\big((\text{pullback } p)(L),\, p^{-1}(U)\big)$$
--   such that for every section $s \in \Gamma(L, U)$ one has $\beta(1 \otimes s) = \eta_L(s)$, where $\eta_L$ is the component at $U$ of the unit of the adjunction between inverse image and direct image of modules along $p$. By $B$-linearity $\beta$ is therefore the canonical base-change map $b \otimes s \mapsto b \cdot p^{*}s$, and the assertion is that this map is bijective.
--
--   This is the affine base-change formula $\Gamma(\operatorname{Spec} B, p^{*}\widetilde{M}) = B \otimes_{A} M$ for the inverse image of a quasi-coherent sheaf, specialised to an invertible sheaf and phrased for an arbitrary morphism of schemes over an affine open whose preimage is affine (as happens for every affine open when $p$ is an affine morphism, in particular a closed immersion). It is used to identify sections of a restricted or pulled-back line bundle with a base change, and feeds into the computations of Euler characteristics of twists and of pushforwards along adic thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
    {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) :
    letI := (p.app U).hom.toAlgebra
    ∃ β : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback p).obj L, p ⁻¹ᵁ U),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L).app U) s := by sorry
