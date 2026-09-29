-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- name    : AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/32a0b307-86ee-523a-be70-f57026bc8fc0
-- title:
--   Algebraisation of a compatible system of closed subschemes of adic thickenings
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal, and suppose $R$ is $I$-adically complete. Let $P$ be a scheme with a morphism $p : P \to \operatorname{Spec} R$, and suppose that for some $N$ there is a closed immersion $\iota_P$ of $P$ into $\operatorname{Proj}$ of the homogeneous-submodule graded algebra of $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,(N+1))\,R$, i.e. into $\mathbb{P}^N_R$, such that $\iota_P$ followed by the structural projection `ProjSpace.π R N` equals $p$. For each $n \in \mathbb{N}$ write $P_n =$ `adicThickening p I n`, the fibre product of $p$ with $\operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, let `adicThickeningι p I n` be the canonical morphism $P_n \to P$ and `adicThickeningTransition p I n` the morphism $P_n \to P_{n+1}$ induced by this morphism together with $P_n \to \operatorname{Spec}(R/I^{n+1})$ composed with $\operatorname{Spec}$ of the quotient map $R/I^{n+2} \to R/I^{n+1}$. Given quasi-coherent ideal sheaf data $J_n$ on $P_n$ for every $n$, whose pullbacks satisfy $(J_{n+1}).\mathrm{comap}$ along the transition morphism $= J_n$, the conclusion asserts the existence of ideal sheaf data $J$ on $P$ with $J.\mathrm{comap}$ along `adicThickeningι p I n` equal to $J_n$ for every $n$.
--
--   This is Grothendieck's existence (algebraisation) theorem for closed subschemes in the projective case: a compatible system of closed subschemes $Z_n \subseteq P_n$ of the $I$-adic thickenings of a projective $R$-scheme $P$ comes from a single closed subscheme $Z \subseteq P$. It is used to obtain existence and uniqueness of morphisms prescribed on all thickenings ([`AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj)), the graph construction of formal algebraisation, and rests on the coherent-sheaf existence theorem for closed immersions into projective space over an adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιP : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιP : IsClosedImmersion ιP)
    (hιPp : ιP ≫ ProjSpace.π R N = p)
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by sorry
