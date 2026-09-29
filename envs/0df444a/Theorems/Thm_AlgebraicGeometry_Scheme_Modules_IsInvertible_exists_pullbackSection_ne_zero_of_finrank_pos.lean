-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullbackSection_ne_zero_of_finrank_pos
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullbackSection_ne_zero_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1e3e9d53-db89-5407-88d9-5e2c781e9dba
-- title:
--   Invertible sheaf with h⁰>0 has a section nonvanishing at a k-point
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme and let $f : X \to \operatorname{Spec} k$ be a morphism, with $X$ reduced and $f$ locally of finite type. Let $M$ be a sheaf of modules on $X$ (an object of `X.Modules`) satisfying the project's invertibility predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \subseteq X$ containing $x$ such that the pullback of $M$ along the inclusion $U.\iota$ is isomorphic to the unit sheaf of modules `SheafOfModules.unit` on $U$. Equip $\Gamma(X,\top)$ with the $k$-algebra structure coming from the ring map $(\Gamma\mathrm{Spec}\text{-}\mathrm{iso})^{-1} \circ f^{\sharp}$ on global sections, and $\Gamma(M,\top)$ with the induced $k$-module structure by restriction of scalars; assume $0 < \operatorname{finrank}_k \Gamma(M,\top)$ (so in particular, in the Lean convention, this rank is finite). The conclusion is the existence of a morphism $\theta : \mathbf 1_{X.\mathrm{Modules}} \to M$ from the unit object, i.e. a global section of $M$, and of a morphism $u : \operatorname{Spec} k \to X$ with $u \circ f = \mathrm{id}_{\operatorname{Spec} k}$, that is a $k$-point of $X$ over $k$, such that `Scheme.Modules.pullbackSection u θ`, namely the composite of the inverse of the pullback-unit isomorphism with $u^*\theta$, is a nonzero morphism $\mathbf 1_{(\operatorname{Spec} k).\mathrm{Modules}} \to u^*M$.
--
--   This is the standard statement that on a reduced scheme locally of finite type over an algebraically closed field, an invertible sheaf with a nonzero global section has a section not vanishing at some $k$-point; positivity of $h^0$ is used only through the nontriviality of $\Gamma(X,\mathcal M)$. It feeds the computations of stabilisers for polarisations, where one must produce a rigidified line bundle section that survives pullback to a $k$-point, including the dual-numbers variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullbackSection_ne_zero_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullbackSection_ne_zero_of_finrank_pos
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hpos : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(M, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
      0 < Module.finrank k Γ(M, ⊤)) :
    ∃ (θ : 𝟙_ X.Modules ⟶ M) (u : Spec (CommRingCat.of k) ⟶ X), u ≫ f = 𝟙 _ ∧
      Scheme.Modules.pullbackSection u θ ≠ 0 := by sorry
