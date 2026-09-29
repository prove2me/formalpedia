-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_mul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/22c647c0-704c-5e7c-8b35-50030336e2aa
-- title:
--   Rescaling a Čech trivialisation by units on the charts
-- statement:
--   Let $Y$ be a scheme, let $\mathcal V$ be an ordered affine cover of $Y$ (a finite, linearly ordered index type $\iota$ together with opens $\mathcal V.U\,a$ that are affine and cover $Y$), and let $\mathcal M$ be an object of `Y.Modules`. Let $\tau$ be a Čech trivialisation of $\mathcal M$ on $\mathcal V$, i.e. for each $a \in \iota$ an isomorphism $\tau a$ from the pullback of $\mathcal M$ to $\mathcal V.U\,a$ onto the unit sheaf of modules on $\mathcal V.U\,a$. Let $c, c'$ be families of sections $c\,a, c'\,a \in \Gamma(Y, \mathcal V.U\,a)$ with $c\,a \cdot c'\,a = 1$ for every $a$, so each $c\,a$ is a unit with inverse $c'\,a$. Then there is a Čech trivialisation $\tau'$ of $\mathcal M$ on the same cover such that, first, for every $a$ the section attached by `unitAutSection` to the automorphism $(\tau a)^{-1}$ followed by $\tau' a$ of the unit sheaf on $\mathcal V.U\,a$ — namely the image of $1$ under its component at the top open, read in $\Gamma(Y,\mathcal V.U\,a)$ — equals $c\,a$; and second, for every $s : \mathcal V.\mathrm{Idx}\,1$, that is every strictly increasing pair $s_0 < s_1$ in $\iota$, the transition section of $\tau'$ at $s$ in $\Gamma(Y, \mathcal V.U\,s_0 \sqcap \mathcal V.U\,s_1)$ equals that of $\tau$ multiplied by the restriction of $c'\,s_0$ and the restriction of $c\,s_1$ to that intersection.
--
--   This is the standard bookkeeping for rescaling a local trivialisation of a module by units on the members of an affine cover: the change-of-trivialisation section on each chart is prescribed to be $c\,a$, and the Čech transition cocycle is multiplied by the coboundary $c'_{s_0} c_{s_1}$. It is used in [`AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range`](thm.html#AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range), where suitable choices of the units normalise the transition sections before the trivialisations are glued.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_mul_mul
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (c c' : ∀ a : 𝒱.ι, Γ(Y, 𝒱.U a)) (hc : ∀ a : 𝒱.ι, c a * c' a = 1) :
    ∃ τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜,
      (∀ a : 𝒱.ι, Scheme.Modules.unitAutSection (𝒱.U a) ((τ a).symm ≪≫ τ' a) = c a) ∧
      ∀ s : 𝒱.Idx 1,
        τ'.transition s = τ.transition s *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 0)).op).hom (c' (s.1 0)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 1)).op).hom (c (s.1 1)) := by sorry
