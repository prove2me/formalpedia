-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/de6c53a1-e8b1-5c7f-b015-6f22e7e3e610
-- title:
--   Frames for L^{⊗ 3} on a cover, from the theorem of the square
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme and $t : X \to \operatorname{Spec} k$ a proper morphism with $X$ integral, the object $\mathrm{Over.mk}\ t$ of schemes over $\operatorname{Spec} k$ being equipped with a group-object structure whose multiplication is commutative. Let $L$ be a module over $X$ that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module over $\mathcal{O}_U$. Assume the theorem of the square: for all $k$-points $x, y$ of $X$, i.e. sections of $t$ viewed as morphisms $\mathrm{Over.mk}\,(\mathbb{1}_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\ t$, the pullbacks of $L$ along the underlying maps $X \to X$ of the translations by $x$ and by $y$ have tensor product isomorphic to the tensor product of the pullback along translation by $xy$ with $L$. Let $\theta : \mathcal{O}_X \to L$ be a nonzero morphism from the unit module. Then there exist $N \in \mathbb{N}$, global sections $\sigma_0, \dots, \sigma_N$ of $L^{\otimes 3} = ((\mathcal{O}_X \otimes L) \otimes L) \otimes L$ and opens $U_0, \dots, U_N$ of $X$ whose supremum is $\top$, such that each $\sigma_i$ is a frame on $U_i$: for every open $W \subseteq U_i$, the map $\Gamma(X, W) \to \Gamma(L^{\otimes 3}, W)$ sending $g$ to $g$ times the restriction of $\sigma_i$ is bijective.
--
--   This is the base-point freeness of $|3L|$ for a line bundle with a nonzero section on a proper integral commutative group scheme over an algebraically closed field, in the form of an explicit finite cover by opens on which $L^{\otimes 3}$ is free on a single global section; the translates of $\theta$ supplying the sections come from the theorem of the square. It feeds the construction of finite presentations by sections of the theta bundle on relative Picard schemes and, through that, the treatment of invertible modules on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L) (hθ : θ ≠ 0) :
    ∃ (N : ℕ) (σ : Fin (N + 1) → Γ(L.tensorPow 3, ⊤)) (U : Fin (N + 1) → X.Opens),
      iSup U = ⊤ ∧ ∀ i, Scheme.Modules.IsFrameOn (σ i) (U i) := by sorry
