-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/04b33307-8ed9-5990-bbf4-aa2207f092c1
-- title:
--   Cocycle isomorphism over a kernel pair gives a descent datum
-- statement:
--   Let $c : X' \to X$ be a morphism of schemes, let $a_1, a_2 : X'' \to X'$ be such that the square with sides $a_1, a_2$ over $c, c$ is cartesian (so $X''$ is the kernel pair of $c$), and let $b_{12}, b_{13}, b_{23} : X''' \to X''$ satisfy $a_1 \circ b_{12} = a_1 \circ b_{13}$, $a_2 \circ b_{12} = a_1 \circ b_{23}$ and $a_2 \circ b_{13} = a_2 \circ b_{23}$, with the square with sides $b_{12}, b_{23}$ over $a_2, a_1$ cartesian. Let $L'$ be an $\mathcal O_{X'}$-module, i.e. an object of `X'.Modules`, and let $\psi : a_1^* L' \cong a_2^* L'$ be an isomorphism in `X''.Modules`. Assume the cocycle condition: the composite, in diagrammatic order, of the inverse of the comparison isomorphism attached to $a_1 \circ b_{12} = a_1 \circ b_{13}$, the inverse of the comparison $b_{12}^* a_1^* \cong (a_1 \circ b_{12})^*$, the isomorphism $b_{12}^*\psi$, the comparison $b_{12}^* a_2^* \cong (a_2 \circ b_{12})^*$, the comparison attached to $a_2 \circ b_{12} = a_1 \circ b_{23}$, the inverse comparison for $b_{23}^* a_1^*$, the isomorphism $b_{23}^*\psi$, the comparison for $b_{23}^* a_2^*$ and the inverse comparison attached to $a_2 \circ b_{13} = a_2 \circ b_{23}$, equals the composite of the inverse comparison for $b_{13}^* a_1^*$, the isomorphism $b_{13}^*\psi$ and the comparison for $b_{13}^* a_2^*$; both sides are isomorphisms $(a_1 \circ b_{13})^* L' \cong (a_2 \circ b_{13})^* L'$. The conclusion asserts the existence of a descent datum $D$ for the pseudofunctor $Y \mapsto \mathcal O_Y$-modules, $f \mapsto f^*$ (the pseudofunctor `Scheme.Modules.pseudofunctor` followed by `Bicategory.Adj.forget₁`) relative to the one-element family of morphisms indexed by `Unit` with value $c$, such that $D.\mathrm{obj}\,i = L'$ for every index $i$.
--
--   This is the packaging step converting a Čech-type cocycle datum over the kernel pair and triple overlap of a single morphism into Mathlib's notion of descent datum for the pseudofunctor of quasi-coherent-style module categories with pull-back; no flatness, affineness or invertibility hypotheses enter. It feeds the effective-descent input in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback) and in [`AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_isPullback
    {X X' X'' X''' : Scheme.{u}} (c : X' ⟶ X) (a₁ a₂ : X'' ⟶ X') (ha : IsPullback a₁ a₂ c c)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (hb : IsPullback b₁₂ b₂₃ a₂ a₁)
    (L' : X'.Modules)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => c),
      ∀ i, D.obj i = L' := by sorry
