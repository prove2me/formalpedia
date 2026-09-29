-- Prove2me | Theorems.Thm_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem
-- name    : AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9f2f3e62-3b48-5e4f-a007-1bd159dd5197
-- title:
--   Rational points linked by smooth proper curves
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme and let $y \colon Y \to \operatorname{Spec} k$ be a proper morphism, with $Y$ integral. Let $S$ be an arbitrary set of morphisms $\operatorname{Spec} k \to Y$. Assume: (i) there is a morphism $y_0 \colon \operatorname{Spec} k \to Y$ which is a section of $y$, i.e. $y_0$ followed by $y$ is the identity of $\operatorname{Spec} k$, and $y_0 \in S$; (ii) $S$ is stable along smooth proper curves in the following sense: for every scheme $C$ and every morphism $c \colon C \to \operatorname{Spec} k$ which is proper and smooth of relative dimension $1$, with $C$ integral, for every $\psi \colon C \to Y$ such that $\psi$ followed by $y$ equals $c$, and for all sections $p, q$ of $c$, if $p$ followed by $\psi$ lies in $S$ then $q$ followed by $\psi$ lies in $S$. Then every section $y_1$ of $y$ lies in $S$. Thus any $k$-point of $Y$ is reached from $y_0$ by the stability hypothesis; no constraint is imposed on members of $S$ that are not sections of $y$.
--
--   This is the curve lemma used in the proof of the theorem of the cube: the classical statement that two points of an irreducible variety lie on an irreducible curve, combined with normalisation and completion of that curve, packaged as an induction principle for sets of $k$-rational points that are stable along smooth proper integral curves. It is consumed by the results on line bundles on a triple product that are trivial on the three coordinate slices, namely [`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices) and its monoidal variant, and it is proved from [`Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one`](thm.html#Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one) together with [`AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one`](thm.html#AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [IsIntegral Y]
    (S : Set (Spec (CommRingCat.of k) ⟶ Y))
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _) (h₀ : y₀ ∈ S)
    (hS : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
      [SmoothOfRelativeDimension 1 c] [IsIntegral C] (ψ : C ⟶ Y), ψ ≫ y = c →
      ∀ p q : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ → q ≫ c = 𝟙 _ → p ≫ ψ ∈ S → q ≫ ψ ∈ S)
    (y₁ : Spec (CommRingCat.of k) ⟶ Y) (hy₁ : y₁ ≫ y = 𝟙 _) : y₁ ∈ S := by sorry
