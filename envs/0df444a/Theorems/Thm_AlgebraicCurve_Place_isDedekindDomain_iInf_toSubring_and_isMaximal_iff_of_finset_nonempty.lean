-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
-- name    : AlgebraicCurve.Place.isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c4035210-50d0-5d35-b23d-4183f6468634
-- title:
--   Holomorphy rings off a non-empty finite set of places
-- statement:
--   Let $k$ be an algebraically closed field and $K$ a field extension of $k$ which is essentially of finite type over $k$ and satisfies `IsCurveOver k K`: every non-zero $f \in K$ has a degree-zero divisor whose multiplicity at each place is $\operatorname{ord}_v f$, each place of $K/k$ has residue field finite over $k$, and $\Omega_{K/k}$ is free of rank $1$ over $K$. Here a place $v$ is a valuation subring of $K$ containing $k$, different from $K$ itself, and a principal ideal ring, and $\operatorname{ord}_v f = -\log$ of the associated $\mathbb{Z}^{m0}$-valued adic valuation at $f$. Let $N$ be a non-empty finite set of places of $K/k$ and let $R_N \subseteq K$ be the intersection (infimum of subrings) of the valuation rings of all places $Q \notin N$. The assertion is fourfold: $R_N$ is a Dedekind domain; every maximal ideal $\mathfrak{m}$ of $R_N$ equals $\{g \in R_N : g = 0 \text{ or } \operatorname{ord}_Q g > 0\}$ for a unique place $Q \notin N$; conversely, for every $Q \notin N$ this set is a maximal ideal of $R_N$; and every non-zero prime ideal of $R_N$ is maximal.
--
--   This is the standard description of the holomorphy ring $R_N$ of an algebraic function field of one variable over an algebraically closed constant field, i.e. the affine coordinate ring of the curve with the points of $N$ removed, together with the bijection between its maximal ideals and the places off $N$. It is used in the construction of affinoid charts near supersingular points on modular curves, where affine models of curves minus finitely many points are required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicCurve

theorem Place.isDedekindDomain_iInf_toSubring_and_isMaximal_iff_of_finset_nonempty
    {k : Type*} [Field k] [IsAlgClosed k] {K : Type*} [Field K] [Algebra k K]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    (N : Finset (Place k K)) (hN : N.Nonempty) :
    IsDedekindDomain ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring) ∧
    (∀ 𝔪 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal →
      ∃! Q : Place k K, Q ∉ N ∧
        ∀ g : ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ Q : Place k K, Q ∉ N →
      ∃ 𝔪 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal ∧
        ∀ g : ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : K) = 0 ∨ 0 < Q.ord (g : K)) ∧
    (∀ 𝔭 : Ideal ↥(⨅ (Q : Place k K) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal) := by sorry
