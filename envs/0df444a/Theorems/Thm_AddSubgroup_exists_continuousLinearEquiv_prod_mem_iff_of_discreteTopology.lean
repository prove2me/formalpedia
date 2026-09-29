-- Prove2me | Theorems.Thm_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
-- name    : AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/eda6beb8-20c3-5343-b355-601e1956953a
-- title:
--   Adapted coordinates for a discrete subgroup of a real vector space
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space (a normed additive commutative group with a real normed space structure and finite dimension over $\mathbb{R}$), and let $L$ be an additive subgroup of $V$ whose induced subspace topology is discrete. The assertion is that there exist natural numbers $a$ and $b$ and a continuous $\mathbb{R}$-linear isomorphism with continuous inverse $T : (\mathrm{Fin}\,a \to \mathbb{R}) \times (\mathrm{Fin}\,b \to \mathbb{R}) \xrightarrow{\sim} V$, that is $T : \mathbb{R}^a \times \mathbb{R}^b \cong V$, such that for every $x \in V$ one has $x \in L$ if and only if there is an integer vector $k : \mathrm{Fin}\,a \to \mathbb{Z}$ with $T\big((i \mapsto (k\,i : \mathbb{R})),\, 0\big) = x$. Thus $T$ carries the standard coordinate lattice $\mathbb{Z}^a \times \{0\}$ of the first factor exactly onto $L$. No bound on $a$ or $b$ is asserted explicitly, nor is the freeness of $L$ stated separately; both are consequences of the displayed bijection.
--
--   This is the classical structure theorem for discrete subgroups of a finite-dimensional real vector space, in the form of a choice of linear coordinates in which the subgroup becomes the integral lattice of a coordinate subspace. It is used to put a sum over an arbitrary discrete subgroup into the coordinate shape $\mathbb{Z}^a \times \{0\} \subseteq \mathbb{R}^a \times \mathbb{R}^b$ required by Poisson summation, in the construction of an atomless measure attached to lattice sums against a Schwartz window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x := by sorry
