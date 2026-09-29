-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd
-- name    : AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8bd9711f-6352-58fc-b1cc-b0f688b62567
-- title:
--   Segre: external tensor product of closed immersions by sections
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $Y$ be schemes, and let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms. Let $L$ be a module over $X$ and $M$ a module over $Y$, and assume each satisfies `ClosedImmersionBySections` over its structure morphism: for $L$ there are an $N$ and sections $\sigma_0,\dots,\sigma_N \in \Gamma(L,\top)$ together with a morphism $\varphi : X \to \operatorname{Proj}$ of the $R$-algebra of homogeneous polynomials in $N+1$ variables, lying over $f$ via the projection $\varphi$ followed by $\pi$ equals $f$, such that on any open $V$ contained in $\varphi^{-1}D_+(X_i)$ multiplication by $\Gamma(X,V)$ on the restriction of $\sigma_i$ is a bijection onto $\Gamma(L,V)$, the sections $\sigma_i,\sigma_j$ are related over $\varphi^{-1}D_+(X_i)$ by the pullback of the ratio $X_j/X_i$, and $\varphi$ is a closed immersion; similarly for $M$ with $g$. The conclusion is that the module $(\text{pr}_1)^{*}L \otimes (\text{pr}_2)^{*}M$ on the fibre product $X \times_{\operatorname{Spec} R} Y$, formed by pulling back along the two projections and taking the monoidal product, satisfies the same predicate over the structure morphism $\text{pr}_1$ followed by $f$.
--
--   This is the Segre embedding statement in the form: if $L$ and $M$ are very ample in the naive sense that a finite tuple of global sections presents a closed immersion into projective space over $R$, then the external tensor product $L \boxtimes M$ is very ample on $X \times_R Y$ (cf. Hartshorne II, Ex. 5.12; EGA II 4.3.3). It is used in the construction of the scheme representing the Hilbert functor of a proper flat morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.lean

import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (L : X.Modules) (hL : Scheme.Modules.ClosedImmersionBySections L f)
    (M : Y.Modules) (hM : Scheme.Modules.ClosedImmersionBySections M g) :
    Scheme.Modules.ClosedImmersionBySections
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗ (Scheme.Modules.pullback (pullback.snd f g)).obj M)
      (pullback.fst f g ≫ f) := by sorry
