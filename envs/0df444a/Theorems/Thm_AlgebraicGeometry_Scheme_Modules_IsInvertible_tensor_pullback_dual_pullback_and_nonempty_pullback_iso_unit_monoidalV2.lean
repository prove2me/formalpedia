-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5a29cbf2-6b22-5bde-9cdc-266f246876a0
-- title:
--   Rigidification L ⊗ q^*((σ^*L)^∨) along a section
-- statement:
--   Let $T$ and $P$ be schemes, let $\sigma \colon T \to P$ and $q \colon P \to T$ be morphisms with $\sigma$ followed by $q$ equal to $\mathbb{1}_T$, so that $\sigma$ is a section of $q$, and let $L$ be an object of the category $P.\mathrm{Modules}$ of sheaves of modules on $P$ which satisfies `Scheme.Modules.IsInvertible`, i.e. every point of $P$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow P$ admits an isomorphism to the unit sheaf of modules on $U$. Writing $M^\vee$ for the internal hom $\underline{\mathrm{Hom}}(M, \mathbb{1})$ into the monoidal unit, the conclusion is the conjunction of two assertions about the rigidified module $L \otimes q^*\big((\sigma^*L)^\vee\big)$: first, it again satisfies `Scheme.Modules.IsInvertible`, i.e. it is locally isomorphic to the unit sheaf on a neighbourhood of each point of $P$; second, the type of isomorphisms $\sigma^*\big(L \otimes q^*((\sigma^*L)^\vee)\big) \cong \mathbb{1}_{T.\mathrm{Modules}}$ is nonempty, the unit being that of the monoidal structure on $T.\mathrm{Modules}$. Both tensor products and the dual are taken for that monoidal structure on sheaves of modules.
--
--   This is the standard rigidification construction for line bundles on a scheme equipped with a section: any invertible module may be modified by a pullback from the base so as to become trivial along the section, as in the construction of the relative Picard functor. It is used in the present development by the statements on rigidified gluing and on pullbacks of modules that are locally isomorphic to a pullback from the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible
        (L ⊗ (Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj
          (L ⊗ (Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))) ≅
        𝟙_ T.Modules) := by sorry
