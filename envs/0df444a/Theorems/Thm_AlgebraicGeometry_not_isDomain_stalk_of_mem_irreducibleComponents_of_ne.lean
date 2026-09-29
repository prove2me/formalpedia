-- Prove2me | Theorems.Thm_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
-- name    : AlgebraicGeometry.not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/b4221463-043a-534c-be55-f6e1e947a775
-- title:
--   A point on two components has non-domain stalk
-- statement:
--   Let $Y$ be a scheme (in a fixed universe), let $y$ be a point of its underlying topological space, and let $Z_1, Z_2$ be subsets of that space which are both irreducible components of $Y$, i.e. maximal elements of the collection of irreducible subsets. Assume $Z_1 \neq Z_2$ and that $y$ lies in $Z_1$ and in $Z_2$. The conclusion is that the stalk $\mathcal{O}_{Y,y}$ of the structure sheaf of $Y$ at $y$, formed as the stalk of the presheaf `Y.presheaf` at $y$, does not satisfy `IsDomain`: it is not a nontrivial commutative ring without zero divisors. No finiteness or Noetherian hypothesis is imposed on $Y$, and the statement is about the abstract ring structure of the stalk only.
--
--   This is the standard local criterion that a point lying on two distinct irreducible components of a scheme is a singular (indeed non-unibranch, non-domain) point of the local ring; equivalently, the stalk at such a point has at least two minimal primes. It is used in the project to detect singular or reducible behaviour at crossings, feeding into [`AlgebraicGeometry.exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension`](thm.html#AlgebraicGeometry.exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension) and into the analysis of fibres of the modular curve model in [`ModularCurve.XOneP.germ_mem_maximalIdeal_and_not_isRegularLocalRing_fibre_fst_of_mem_irreducibleComponents_pair_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.germ_mem_maximalIdeal_and_not_isRegularLocalRing_fibre_fst_of_mem_irreducibleComponents_pair_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_not_isDomain_stalk_of_mem_irreducibleComponents_of_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.not_isDomain_stalk_of_mem_irreducibleComponents_of_ne
    (Y : Scheme.{u}) (y : ↥Y) (Z₁ Z₂ : Set ↥Y)
    (hZ₁ : Z₁ ∈ irreducibleComponents ↥Y) (hZ₂ : Z₂ ∈ irreducibleComponents ↥Y)
    (hne : Z₁ ≠ Z₂) (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) :
    ¬ IsDomain (Y.presheaf.stalk y) := by sorry
