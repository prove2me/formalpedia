-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_tensor_forall_transition_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/bf3d1213-48b8-5030-aa1b-9ce77e57f4c5
-- title:
--   Tensoring Čech trivialisations multiplies transition sections
-- statement:
--   Let $Y$ be a scheme and let $\mathcal{V}$ be an ordered affine cover of $Y$: a finite linearly ordered index type $\mathcal{V}.\iota$ together with opens $\mathcal{V}.U\,i$, each affine, whose supremum is $\top$. Let $\mathcal{L}$ and $\mathcal{M}$ be objects of $Y$`.Modules`. A Čech trivialisation of an object $\mathcal{N}$ on $\mathcal{V}$ is, by definition, a family assigning to each index $a$ an isomorphism between the pullback of $\mathcal{N}$ along the open immersion $(\mathcal{V}.U\,a).\iota$ and the unit module sheaf on the scheme $\mathcal{V}.U\,a$. Given such trivialisations $\tau$ of $\mathcal{L}$ and $\tau'$ of $\mathcal{M}$, the assertion is that there is a Čech trivialisation $\sigma$ of the monoidal product $\mathcal{L}\otimes\mathcal{M}$ on $\mathcal{V}$ whose transition sections are the pointwise products: for every $s : \mathcal{V}.\mathrm{Idx}\,1$, i.e. every strictly monotone $s : \mathrm{Fin}\,2 \to \mathcal{V}.\iota$ (equivalently a pair $s_0 < s_1$), one has $\sigma.\mathrm{transition}\,s = \tau.\mathrm{transition}\,s \cdot \tau'.\mathrm{transition}\,s$ in $\Gamma(Y, \mathcal{V}.U\,s_0 \sqcap \mathcal{V}.U\,s_1)$. Here the transition section attached to $s$ is the section of the structure sheaf over that intersection obtained by evaluating at $1$ the automorphism of the unit module sheaf given by the restriction of the trivialisation over $\mathcal{V}.U\,s_0$ inverted and followed by the restriction over $\mathcal{V}.U\,s_1$.
--
--   This is the multiplicativity of Čech transition cocycles under tensor product of invertible modules, in the form needed for the cover-indexed bookkeeping used here. It is used for the additivity of the Picard obstruction cocycle under tensor product, and in recognising when two trivialisations have equal transition data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_tensor_forall_transition_eq_mul
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓛 𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛) (τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ σ : Scheme.Modules.CechTrivialisation 𝒱 (𝓛 ⊗ 𝓜),
      ∀ s : 𝒱.Idx 1, σ.transition s = τ.transition s * τ'.transition s := by sorry
