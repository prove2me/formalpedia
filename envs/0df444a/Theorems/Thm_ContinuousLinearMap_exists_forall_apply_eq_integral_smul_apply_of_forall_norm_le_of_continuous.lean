-- Prove2me | Theorems.Thm_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
-- name    : ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/28e3873b-e124-5247-95dc-869c639bbb78
-- title:
--   Weighted Haar average of a bounded continuous representation
-- statement:
--   Let $C$ be a compact Hausdorff topological group, equipped with a Borel measurable structure compatible with its topology, and let $\mu$ be a Haar measure on $C$ which is a probability measure. Let $H$ be a complex Hilbert space (a complete normed complex inner product space). Let $S : C \to (H \to_{L[\mathbb{C}]} H)$ be a homomorphism of monoids into the bounded $\mathbb{C}$-linear endomorphisms of $H$, let $B \in \mathbb{R}$ satisfy $\|S(c)\| \le B$ for all $c \in C$, and suppose $S$ is strongly continuous, i.e. $c \mapsto S(c)v$ is continuous for each $v \in H$. Let $w : C \to \mathbb{C}$ be continuous. The assertion is that there exists a bounded operator $A$ on $H$ with the following four properties: (i) $A v = \int_C w(c)\,S(c)v \, d\mu(c)$ for every $v \in H$ (a Bochner integral); (ii) for every real $M$ with $\|w(c)\| \le M$ for all $c$, one has $\|Av\| \le M B \|v\|$ for all $v$; (iii) for every $\mathbb{C}$-submodule $L$ of $H$ whose underlying set is closed and which satisfies $S(c)(L) \subseteq L$ for all $c \in C$, one has $A(L) \subseteq L$; and (iv) for every bounded operator $T$ on $H$ commuting with $S(c)$ for all $c$, $T$ commutes with $A$ (equality of the composites $T \circ A$ and $A \circ T$ as continuous linear maps).
--
--   This is the standard construction of a weighted average $\int_C w(c) S(c)\,d\mu(c)$ of a uniformly bounded strongly continuous representation of a compact group on a Hilbert space, together with the three properties of such averages that are used in practice: the operator norm bound, preservation of closed invariant subspaces, and commutation with the commutant of the representation. It serves as the averaging engine behind the construction of idempotent level-average and archimedean-type projectors on spaces of cusp forms, and is cited by [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector) and [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)
    (w : C → ℂ) (hw : Continuous w) :
    ∃ A : H →L[ℂ] H,
      (∀ v : H, A v = ∫ c, (w c) • (S c v) ∂μ) ∧
      (∀ M : ℝ, (∀ c : C, ‖w c‖ ≤ M) → ∀ v : H, ‖A v‖ ≤ M * B * ‖v‖) ∧
      (∀ L : Submodule ℂ H, IsClosed (L : Set H) →
        (∀ c : C, L.map (S c : H →ₗ[ℂ] H) ≤ L) → L.map (A : H →ₗ[ℂ] H) ≤ L) ∧
      (∀ T : H →L[ℂ] H, (∀ c : C, T.comp (S c) = (S c).comp T) → T.comp A = A.comp T) := by sorry
