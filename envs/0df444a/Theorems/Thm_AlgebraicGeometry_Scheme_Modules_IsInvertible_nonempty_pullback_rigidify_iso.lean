-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/006c54a8-d09a-5db9-8270-d2b5a305d100
-- title:
--   Rigidification commutes with base change
-- statement:
--   Let $T, P, T', P'$ be schemes, with morphisms $\sigma \colon T \to P$, $q \colon P \to T$, $\sigma' \colon T' \to P'$, $q' \colon P' \to T'$, and let $\psi \colon T' \to T$ and $\Psi \colon P' \to P$ be morphisms compatible with these data in the sense that $\sigma'$ followed by $\Psi$ equals $\psi$ followed by $\sigma$, and $\Psi$ followed by $q$ equals $q'$ followed by $\psi$. Let $L$ be a module on $P$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $P$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow P$ is isomorphic to the unit module on $U$. Writing $\operatorname{rigidify}_{\sigma,q}(M) = M \otimes q^{*}\bigl((\sigma^{*}M)^{\vee}\bigr)$, where the dual is the internal hom into the unit object of the monoidal category of modules, the assertion is that the type of isomorphisms $$\Psi^{*}\bigl(\operatorname{rigidify}_{\sigma,q}(L)\bigr) \;\cong\; \operatorname{rigidify}_{\sigma',q'}\bigl(\Psi^{*}L\bigr)$$ in the category of modules on $P'$ is nonempty; no particular isomorphism is named, and no naturality or coherence is claimed.
--
--   This is the base-change compatibility of the rigidification of a line bundle along a section, as used in the construction of the relative Picard functor of rigidified line bundles. It is invoked by the statements comparing twist modules and rigidified line bundles with their pullbacks along a base change, including [`AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback`](thm.html#AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback) and its variants for modules supported in a closed subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso.lean

import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    {T P T' P' : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} {σ' : T' ⟶ P'} {q' : P' ⟶ T'}
    (ψ : T' ⟶ T) (Ψ : P' ⟶ P) (hσ : σ' ≫ Ψ = ψ ≫ σ) (hq : Ψ ≫ q = q' ≫ ψ)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback Ψ).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback Ψ).obj L)) := by sorry
