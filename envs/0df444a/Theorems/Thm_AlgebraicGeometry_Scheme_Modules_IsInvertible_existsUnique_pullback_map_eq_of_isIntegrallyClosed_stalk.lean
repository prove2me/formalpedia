-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/5b26436a-ce16-5ae2-af45-008c217e76b1
-- title:
--   Hartogs extension for maps of invertible modules
-- statement:
--   Let $X$ be a locally Noetherian scheme, all of whose stalks $\mathcal{O}_{X,x}$ are integral domains and are integrally closed, and let $U \subseteq X$ be an open subset containing every point $x$ whose stalk has Krull dimension at most $1$ (so that the complement of $U$ has codimension at least $2$). Let $L$ and $L'$ be $\mathcal{O}_X$-modules which are invertible in the sense that each point of $X$ has an open neighbourhood $V$ on which the pullback of the module along the open immersion $V \hookrightarrow X$ is isomorphic to the unit module $\mathcal{O}_V$, and let $\varphi$ be a morphism from the pullback of $L$ to the pullback of $L'$ along the open immersion $U.\iota : U \to X$. Then, first, there is exactly one morphism $\psi : L \to L'$ of $\mathcal{O}_X$-modules whose pullback along $U.\iota$ equals $\varphi$; and second, for every morphism $\psi : L \to L'$ whose pullback along $U.\iota$ equals $\varphi$, if $\varphi$ is an isomorphism then so is $\psi$. Restriction thus identifies $\operatorname{Hom}_{\mathcal{O}_X}(L, L')$ with $\operatorname{Hom}_{\mathcal{O}_U}(L|_U, L'|_U)$ and detects isomorphy.
--
--   This is the Hartogs-type extension statement for homomorphisms of line bundles on a normal locally Noetherian scheme: morphisms defined away from a closed subset of codimension at least $2$ extend uniquely, and being an isomorphism is inherited by the extension; in particular $L|_U \cong L'|_U$ forces $L \cong L'$. It is used to compare invertible modules on Néron-model and relative Picard constructions, notably in identifying pullbacks of norms of the Poincaré bundle along zero sections with the unit module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (φ : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj L') :
    (∃! ψ : L ⟶ L', (Scheme.Modules.pullback U.ι).map ψ = φ) ∧
      ∀ ψ : L ⟶ L', (Scheme.Modules.pullback U.ι).map ψ = φ → IsIso φ → IsIso ψ := by sorry
