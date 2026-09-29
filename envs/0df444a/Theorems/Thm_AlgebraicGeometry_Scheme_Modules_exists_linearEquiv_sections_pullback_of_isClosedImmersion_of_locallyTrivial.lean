-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/63bac9a4-0284-5d27-a4ab-bbaa538b22e9
-- title:
--   Affine base change of sections along a closed immersion
-- statement:
--   Let $X$ and $Y$ be schemes, let $i \colon Y \to X$ be a closed immersion, and let $M$ be a sheaf of modules on $X$. Assume $M$ is Zariski-locally trivial in the following sense: every point $x \in X$ has an open neighbourhood $V$ such that the restriction of $M$ to $V$, i.e. the pullback of $M$ along the open immersion $V \hookrightarrow X$, is isomorphic to the unit module `SheafOfModules.unit` on $V$ (the structure sheaf of $V$ viewed as a module over itself). Let $U \subseteq X$ be an open subset which is an affine open. Regard $\Gamma(Y, i^{-1}U)$ as a $\Gamma(X,U)$-algebra via the ring homomorphism $\Gamma(X,U) \to \Gamma(Y, i^{-1}U)$ given by $i$ on sections over $U$. Then there exists a $\Gamma(Y, i^{-1}U)$-linear isomorphism
--   $$e \colon \Gamma(Y, i^{-1}U) \otimes_{\Gamma(X,U)} \Gamma(M, U) \xrightarrow{\ \sim\ } \Gamma\bigl(i^{*}M,\, i^{-1}U\bigr)$$
--   such that for every $m \in \Gamma(M,U)$ the element $e(1 \otimes m)$ is the image of $m$ under the component at $U$ of the unit $M \to i_{*}i^{*}M$ of the pullback–pushforward adjunction for $i$. Since the pure tensors $1 \otimes m$ generate the source over $\Gamma(Y, i^{-1}U)$, this normalisation determines $e$ uniquely.
--
--   This is the affine base change statement for sections of an invertible (locally free of rank one) module, specialised to a closed immersion, which is affine, so that $i^{-1}U$ is an affine open of $Y$ whenever $U$ is an affine open of $X$; the proof reduces to the case of a tilde module over a ring map via the isomorphism $\widetilde{\Gamma(M)} \to M$ available for locally trivial modules. It is used in the computations of relative Picard groups and Euler characteristics for two glued smooth curves, in particular for two glued projective lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.lean

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (M : X.Modules)
    (htriv : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, i ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e (1 ⊗ₜ m) = (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U).hom m := by sorry
