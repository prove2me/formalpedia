-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/30068ec7-f53c-516d-875d-16045fe4dbad
-- title:
--   Residue fields of the finite chart over algebraically closed κ
-- statement:
--   Let $R$ be a commutative local ring and $F$ a field equipped with an $R$-algebra structure, and assume the residue field $\kappa = R/\mathfrak m_R$ of $R$ is algebraically closed. Fix $j \in F$ and let $C =$ `chartAlgFin R F j` be the $R$-subalgebra of $F$ consisting of those $x \in F$ that are integral over the $R$-subalgebra $R[j] =$ `Algebra.adjoin R {j}` of $F$. Let $y$ be an ideal of $C$ which is assumed maximal, and suppose that the structure map $R \to C$ carries every element of the maximal ideal $\mathfrak m_R$ into $y$. Then for every $b \in C$ there exists $c \in R$ with $b - c\cdot 1 \in y$, where $c\cdot 1$ denotes the image of $c$ under $R \to C$. Equivalently, the composite $R \to C \to C/y$ is surjective, so that the residue field of $C$ at $y$ is canonically $\kappa$ itself. No finiteness assumption on $C$ over $R$, and no hypothesis $j \neq 0$, is imposed.
--
--   This is the statement that the closed points of the $j$-finite chart lying over the closed point of $\operatorname{Spec} R$ have residue field equal to $\kappa$ when $\kappa$ is algebraically closed; it is a relative form of the Nullstellensatz, resting on Zariski's lemma. It is used in the analysis of supersingular closed points of the $j$-finite chart of the rigid level model, for instance in identifying such points by their $q$-expansions and in comparing them under the diamond/level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

theorem AlgebraicCurve.TwoChartIntegralModel.exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
    {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Algebra R F]
    (hres : IsAlgClosed (ResidueField R)) (j : F)
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (hmy : ∀ r ∈ maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) r ∈ y)
    (b : ↥(chartAlgFin R F j)) : ∃ c : R, b - algebraMap R ↥(chartAlgFin R F j) c ∈ y := by sorry
