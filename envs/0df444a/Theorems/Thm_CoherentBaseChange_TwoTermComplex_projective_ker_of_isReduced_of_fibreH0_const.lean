-- Prove2me | Theorems.Thm_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const
-- name    : CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/bee0eb5d-b022-519e-b69c-2bafdffe353e
-- title:
--   Degree-zero cohomology and base change over a reduced ring
-- statement:
--   Let $R$ be a reduced commutative ring and let $G$ be a two-term complex over $R$, that is, finitely generated free $R$-modules $C^0$, $C^1$ together with an $R$-linear map $d \colon C^0 \to C^1$. Let $c$ be a natural number and suppose that for every prime $\mathfrak p$ of $R$ the fibre invariant $\mathrm{fibreH0}(\mathfrak p)$ equals $c$; by definition this is the dimension, over the residue field $\kappa(\mathfrak p)$ of $\mathfrak p$, of the kernel of the base-changed map $d \otimes_R \kappa(\mathfrak p)$. The conclusion is a conjunction of three assertions: first, $\ker d$ is a projective $R$-module; second, for every commutative $R$-algebra $A$ the comparison map $A \otimes_R \ker d \to \ker(d \otimes_R A)$ — the base change to $A$ of the inclusion $\ker d \hookrightarrow C^0$, corestricted to the kernel of $d \otimes_R A$, which is the $A$-linear map `G.kerBaseChangeHom A` — is bijective; third, for every prime $\mathfrak p$ of $R$ the $\kappa(\mathfrak p)$-vector space $\kappa(\mathfrak p) \otimes_R \ker d$ has dimension $c$.
--
--   This is the affine, degree-zero, two-term-complex form of cohomology and base change over a reduced base: constancy of the fibrewise dimension of $H^0$ forces $\ker d$ to be projective of that rank and its formation to commute with arbitrary base change. It is used in the treatment of two-chart Čech computations, where it supplies projectivity of the degree-zero cohomology together with the bijectivity of the base-change comparison map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.lean

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct
open CoherentBaseChange

theorem CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
    {R : Type u} [CommRing R] [IsReduced R] (G : TwoTermComplex.{u, v} R) {c : ℕ}
    (h0 : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = c) :
    Module.Projective R (LinearMap.ker G.d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A], Function.Bijective (G.kerBaseChangeHom A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
        (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker G.d) = c := by sorry
