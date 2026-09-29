-- Prove2me | Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing
-- name    : AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/3b3a4d34-c661-5792-a9e2-bc18db17794f
-- title:
--   Unique Artin-local liftings imply formally unramified
-- statement:
--   Let $R$ be a commutative ring, $M$ a scheme and $\varpi : M \to \operatorname{Spec} R$ a morphism that is locally of finite type. Assume the following lifting-uniqueness condition: for every pair of commutative rings $T'$ and $T$ such that $T'$ is a local Artinian ring whose residue field is algebraically closed and $T$ is nontrivial, for every ring homomorphism $p : T' \to T$ that is surjective and satisfies $(\ker p)\cdot \mathfrak m_{T'} = 0$ as ideals of $T'$, for every morphism $s : \operatorname{Spec} T' \to \operatorname{Spec} R$ and every morphism $m : \operatorname{Spec} T \to M$ with $m$ followed by $\varpi$ equal to $\operatorname{Spec} p$ followed by $s$, any two morphisms $m_1, m_2 : \operatorname{Spec} T' \to M$ which both lie over $s$ (i.e. $m_i$ followed by $\varpi$ equals $s$) and both restrict to $m$ along $\operatorname{Spec} p$ (i.e. $\operatorname{Spec} p$ followed by $m_i$ equals $m$) are equal. Then $\varpi$ is formally unramified.
--
--   This is the easy half of the infinitesimal criterion for unramifiedness (EGA IV 17.1–17.2): uniqueness of liftings need only be tested on small surjections of Artinian local rings with algebraically closed residue field in order to conclude that the relative sheaf of differentials vanishes. It is used in the project to verify formal unramifiedness of moduli morphisms via a tangent-space computation, and feeds into the corresponding criterion for étaleness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing
    {R : Type u} [CommRing R] {M : Scheme.{u}} (ϖ : M ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∀ m₁ m₂ : Spec (CommRingCat.of T') ⟶ M, m₁ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₁ = m →
          m₂ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₂ = m → m₁ = m₂) :
    FormallyUnramified ϖ := by sorry
