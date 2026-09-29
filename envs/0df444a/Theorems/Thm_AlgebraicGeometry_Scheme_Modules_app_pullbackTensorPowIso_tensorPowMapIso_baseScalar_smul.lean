-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul
-- name    : AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e40fb504-8aa5-5117-affa-625788e35ebc
-- title:
--   Pullback of tensor-power sections respects base scalars
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra, let $X$ and $X'$ be schemes, and let $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$ and $c : X' \to X$ be morphisms such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is a pullback square (`IsPullback c f' f`). Let $L$ be an $\mathcal{O}_X$-module, $L'$ an $\mathcal{O}_{X'}$-module and $e$ an isomorphism from the pullback $c^{*}L$ to $L'$ in $X'.\mathrm{Modules}$. Fix $n \in \mathbb{N}$, $a \in S$ and a section $s \in \Gamma(L^{\otimes n}, \top)$, where $L^{\otimes n}$ is defined recursively by $L^{\otimes 0} = \mathbf{1}$ and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. Write $\Phi$ for the composite isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$, whose first factor `pullbackTensorPowIso` is built recursively from the monoidal comparison isomorphisms of the pullback functor (the unit isomorphism in degree $0$, and the tensor comparison whiskered with the lower-degree isomorphism in degree $n+1$) and whose second factor `tensorPowMapIso e n` is the $n$-fold tensor product of $e$ with itself. Let $\eta$ denote the component at $\top$ of the unit of the adjunction between pullback and pushforward along $c$, evaluated at $L^{\otimes n}$, so $\eta$ sends a global section of $L^{\otimes n}$ to its pullback. Finally, `GradedOAlgebra.baseScalar f a` is the global function $f^{\sharp}(a) \in \Gamma(X, \top)$ obtained by transporting $a$ through the inverse of $\Gamma \circ \operatorname{Spec}$ and applying $f$ on global sections, and similarly for $f'$. The assertion is $\Phi(\eta(f^{\sharp}(a) \cdot s)) = f'^{\sharp}(a_{S'}) \cdot \Phi(\eta(s))$, where $a_{S'}$ is the image of $a$ in $S'$.
--
--   This is the compatibility of pullback of sections of tensor powers with the base scalars coming from the structure morphisms: the canonical identification $c^{*}(L^{\otimes n}) \cong L'^{\otimes n}$ carries the $S$-action through $f$ to the $S'$-action through $f'$. It is used in establishing [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback), where a section ring over $S$ is compared with one over $S'$ after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (n : ℕ) (a : S) (s : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (GradedOAlgebra.baseScalar f a • s))
      = GradedOAlgebra.baseScalar f' (algebraMap S S' a) • ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) s) := by sorry
