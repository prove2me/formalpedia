-- Prove2me | Theorems.Thm_AlgebraicGeometry_isConnected_preimage_and_topologicalKrullDim_eq_of_forall_geometricFibre
-- name    : AlgebraicGeometry.isConnected_preimage_and_topologicalKrullDim_eq_of_forall_geometricFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/1abcbb1d-e147-563e-8489-d7ee169055f6
-- title:
--   Connected fibres of dimension g from geometric fibres
-- statement:
--   Let $R$ be a commutative ring, let $Z$ be a scheme, and let $f : Z \to \operatorname{Spec} R$ be a morphism that is proper, flat and locally of finite presentation. Let $g$ be a natural number, and assume the following about all geometric fibres: for every point $s$ of $\operatorname{Spec} R$, every algebraically closed field $k$ and every ring homomorphism $x : R \to k$ whose kernel is the prime ideal corresponding to $s$, the second projection $Z \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ of the pullback of $f$ along $\operatorname{Spec}(x)$ is smooth, the pullback scheme $Z \times_{\operatorname{Spec} R} \operatorname{Spec} k$ has irreducible underlying space, and the topological Krull dimension of that underlying space equals $g$. Then for every point $s$ of $\operatorname{Spec} R$ the set-theoretic fibre $f^{-1}(s)$, i.e. the preimage of $\{s\}$ under the continuous map underlying $f$, is connected (in particular nonempty), and its topological Krull dimension, computed for the subspace topology, equals $g$.
--
--   This is the passage from hypotheses on all geometric fibres of a proper flat morphism to the topology of its set-theoretic fibres: each fibre is connected of dimension $g$. It is used in the construction of the locus of good reduction for Jacobians and in the projective-embedding statement for framed polarised abelian schemes, where fibrewise connectedness and dimension are needed to recognise an abelian scheme of relative dimension $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isConnected_preimage_and_topologicalKrullDim_eq_of_forall_geometricFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isConnected_preimage_and_topologicalKrullDim_eq_of_forall_geometricFibre
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (g : ℕ)
    (h : ∀ (s : ↥(Spec (CommRingCat.of R))) (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g)
    (s : ↥(Spec (CommRingCat.of R))) :
    _root_.IsConnected (f.base ⁻¹' {s}) ∧ topologicalKrullDim ↥(f.base ⁻¹' {s}) = g := by sorry
