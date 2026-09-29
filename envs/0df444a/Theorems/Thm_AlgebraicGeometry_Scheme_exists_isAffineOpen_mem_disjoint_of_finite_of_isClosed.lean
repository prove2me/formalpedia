-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed
-- name    : AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/60765baf-4506-5e0c-910b-2637e801ef3c
-- title:
--   Affine open neighbourhood avoiding a finite set of closed points
-- statement:
--   Let $X$ be a scheme (in a fixed universe), and let $S$ be a subset of the underlying topological space of $X$ which is finite and each of whose members $s$ is a closed point, i.e. the singleton $\{s\}$ is closed in $X$. Let $x$ be a point of $X$ not belonging to $S$. Then there exists an open subscheme-defining open set $V$ of $X$, that is an element of `X.Opens`, such that $V$ is an affine open of $X$ in the sense of `IsAffineOpen` (the restriction of $X$ to $V$ is an affine scheme), $x$ lies in $V$, and the underlying set of $V$ is disjoint from $S$. Note that the conclusion asserts disjointness of $V$ and $S$ as sets, and nothing about $V$ being contained in any prescribed open set beyond $X \setminus S$.
--
--   This is the standard separation fact that a point of a scheme can be separated from finitely many closed points by an affine open neighbourhood, resting on the fact that the affine opens form a basis of the Zariski topology. It is used in the construction of polarisation data, where the finite kernel of a map attached to a line bundle must be excised from a neighbourhood of a chosen point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed
    {X : Scheme.{u}} (S : Set X) (hS : S.Finite) (hcl : ∀ s ∈ S, IsClosed ({s} : Set X))
    (x : X) (hx : x ∉ S) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Disjoint (V : Set X) S := by sorry
