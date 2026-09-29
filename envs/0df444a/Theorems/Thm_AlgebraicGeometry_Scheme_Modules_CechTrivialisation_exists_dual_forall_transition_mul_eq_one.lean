-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_dual_forall_transition_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/398a6b7f-c8d9-50ee-b416-26e5878bcb05
-- title:
--   Dual of a Čech-trivialised module has inverse transitions
-- statement:
--   Let $Y$ be a scheme, let $\mathcal V$ be an ordered affine cover of $Y$ — a finite linearly ordered index type $\mathcal V.\iota$ together with affine opens $\mathcal V.U_a \subseteq Y$ whose supremum is $\top$ — and let $\mathcal L$ be a sheaf of modules on $Y$. Suppose given $\tau$, a Čech trivialisation of $\mathcal L$ on $\mathcal V$, i.e. for every index $a$ an isomorphism of the pullback of $\mathcal L$ along the open immersion $\mathcal V.U_a \hookrightarrow Y$ with the unit module (structure sheaf as a module over itself) on the scheme $\mathcal V.U_a$. The assertion is that there exists a Čech trivialisation $\sigma$ on the same cover of the dual $\mathcal L^\vee$, defined as the internal hom $\underline{\operatorname{Hom}}(\mathcal L, -)$ evaluated at the monoidal unit of $Y$-modules, such that for every $s : \mathcal V.\mathrm{Idx}\,1$ — that is, every strictly monotone $s : \mathrm{Fin}\,2 \to \mathcal V.\iota$, equivalently every pair $a < b$ — the transition sections of $\sigma$ and of $\tau$ at $s$ are mutually inverse units: $\sigma.\mathrm{transition}\,s \cdot \tau.\mathrm{transition}\,s = 1$ in $\Gamma(Y, \mathcal V.U_a \cap \mathcal V.U_b)$. Here the transition section attached to a trivialisation and to $s$ is obtained by restricting the two chart trivialisations to the intersection, composing the inverse of the first with the second, and reading off the value at $1$ of the resulting automorphism of the unit module.
--
--   This is the standard statement that the dual of a line bundle trivialised on a cover is trivialised on the same cover, with transition functions the inverses of the original ones, formulated for the project's Čech trivialisation data. It feeds the comparison of trivialisations with equal transition functions and the computation that passing to the dual negates the Picard obstruction cocycle of a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one.lean

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

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_dual_forall_transition_mul_eq_one
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓛 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛) :
    ∃ σ : Scheme.Modules.CechTrivialisation 𝒱 (Scheme.Modules.dual 𝓛),
      ∀ s : 𝒱.Idx 1, σ.transition s * τ.transition s = 1 := by sorry
