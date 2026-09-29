-- Prove2me | Theorems.Thm_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
-- name    : AlgebraicGeometry.irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d772af95-8073-5f9a-99c3-e2a471a67908
-- title:
--   Irreducibility criterion via bijectivity on k-points
-- statement:
--   Let $k$ be an algebraically closed field, and let $T$ and $Y$ be schemes equipped with morphisms $f_T : T \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$ that are each locally of finite type and quasi-compact, so that $T$ and $Y$ are of finite type over $k$. Let $u : T \to Y$ be a morphism over $k$, i.e. $u$ followed by $f_Y$ equals $f_T$. Assume the underlying topological space of $Y$ is irreducible and its topological Krull dimension is at most $1$. Assume further that $u$ is injective on $k$-points, in the sense that any two morphisms $x_1, x_2 : \operatorname{Spec} k \to T$ that are sections of $f_T$ and satisfy $x_1$ followed by $u$ equals $x_2$ followed by $u$ coincide; that $u$ is surjective on $k$-points, in the sense that every section $y : \operatorname{Spec} k \to Y$ of $f_Y$ is of the form $x$ followed by $u$ for some section $x$ of $f_T$; and finally that if some point $c$ of $T$ has $\{c\}$ open and closed in $T$, then the underlying set of $T$ is finite. The conclusion is that the underlying topological space of $T$ is irreducible (in particular nonempty).
--
--   An irreducibility criterion for a finite-type scheme over an algebraically closed field that maps bijectively on $k$-points to an irreducible curve or point, the last hypothesis excluding isolated points except in the finite case. It is used in the analysis of coarse moduli schemes for quaternionic curve models, where it supplies geometric connectedness alongside geometric reducedness; the proof identifies $k$-points with closed points via the Nullstellensatz ([`AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton`](thm.html#AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton), [`AlgebraicGeometry.isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType`](thm.html#AlgebraicGeometry.isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType)) and uses density of closed points on finite-type schemes over a field ([`AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType`](thm.html#AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] [IsAlgClosed k] {T Y : Scheme.{u}}
    (fT : T ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fT] [QuasiCompact fT] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (u : T ⟶ Y) (hu : u ≫ fY = fT)
    [IrreducibleSpace ↑Y] (hdim : topologicalKrullDim ↑Y ≤ 1)
    (hinj : ∀ x₁ x₂ : Spec (CommRingCat.of k) ⟶ T, x₁ ≫ fT = 𝟙 _ → x₂ ≫ fT = 𝟙 _ → x₁ ≫ u = x₂ ≫ u → x₁ = x₂)
    (hsurj : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ fY = 𝟙 _ → ∃ x : Spec (CommRingCat.of k) ⟶ T, x ≫ fT = 𝟙 _ ∧ x ≫ u = y)
    (hT : ∀ c : ↑T, IsClopen ({c} : Set ↑T) → Finite ↑T) :
    IrreducibleSpace ↑T := by sorry
