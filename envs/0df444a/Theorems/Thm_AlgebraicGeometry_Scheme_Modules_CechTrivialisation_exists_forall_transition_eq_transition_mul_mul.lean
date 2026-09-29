-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_transition_mul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f83a085e-007f-5003-8f74-ee629fef9383
-- title:
--   Two Čech trivialisations differ by chartwise units
-- statement:
--   Let $Y$ be a scheme, let $\mathcal V$ be an ordered affine cover of $Y$ (a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq Y$, each affine, whose supremum is $\top$), and let $\mathcal M$ be an $\mathcal O_Y$-module. Let $\tau, \tau'$ be two Čech trivialisations of $\mathcal M$ on $\mathcal V$, that is, two families of isomorphisms $\tau_a : (\mathcal M)|_{U_a} \xrightarrow{\ \sim\ } \mathcal O_{U_a}$ (the pullback along the inclusion $U_a \hookrightarrow Y$, compared with the unit sheaf of modules of the structure sheaf of $U_a$), indexed by $a \in \iota$. The assertion is that there exist families of sections $c, c' \in \prod_a \Gamma(Y, U_a)$ such that: $c_a c'_a = 1$ for every $a$; for every $a$, $c_a$ is the section $\mathrm{unitAutSection}$ attached to the automorphism $\tau_a^{-1}$ followed by $\tau'_a$ of the unit sheaf on $U_a$, namely the image of $1$ under that automorphism on global sections of $U_a$, transported to $\Gamma(Y,U_a)$; and for every $s \in \mathcal V.\mathrm{Idx}\,1$, i.e. every strictly monotone $s : \mathrm{Fin}\,2 \to \iota$, the transition section of $\tau'$ at $s$ equals that of $\tau$ at $s$ multiplied by the restrictions to $U_{s(0)} \cap U_{s(1)}$ of $c'_{s(0)}$ and of $c_{s(1)}$. Here the transition section of a trivialisation at $s$ is $\mathrm{unitAutSection}$ of the automorphism of the unit sheaf on $U_{s(0)} \cap U_{s(1)}$ obtained by composing the inverse of the restricted $\tau_{s(0)}$ with the restricted $\tau_{s(1)}$.
--
--   This records that the set of Čech trivialisations of a fixed module on a fixed ordered affine cover is acted on simply by chartwise units, and that the associated family of transition sections changes exactly by the corresponding multiplicative coboundary; it is the direction extracting the units from a pair of trivialisations, complementary to the construction of a new trivialisation from given units. It is used in the comparison of two Picard obstruction cocycles, in [`AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle`](thm.html#AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul.lean

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

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_forall_transition_eq_transition_mul_mul
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    ∃ (c c' : ∀ a : 𝒱.ι, Γ(Y, 𝒱.U a)),
      (∀ a : 𝒱.ι, c a * c' a = 1) ∧
      (∀ a : 𝒱.ι, Scheme.Modules.unitAutSection (𝒱.U a) ((τ a).symm ≪≫ τ' a) = c a) ∧
      ∀ s : 𝒱.Idx 1,
        τ'.transition s = τ.transition s *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 0)).op).hom (c' (s.1 0)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le s 1)).op).hom (c (s.1 1)) := by sorry
