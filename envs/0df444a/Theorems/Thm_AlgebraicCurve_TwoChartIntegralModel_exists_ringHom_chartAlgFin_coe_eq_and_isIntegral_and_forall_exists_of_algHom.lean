-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/bc557384-f056-5111-a2b6-1fb07889432c
-- title:
--   Functoriality and integrality of the finite chart ring along φ
-- statement:
--   Let $R$ be a commutative ring, let $F''$ and $F$ be fields equipped with $R$-algebra structures, let $\varphi \colon F'' \to F$ be an $R$-algebra homomorphism, and let $j'' \in F''$ and $j \in F$ be non-zero elements with $\varphi(j'') = j$. Write $A'' =$ `chartAlgFin R F'' j''` for the $R$-subalgebra of $F''$ consisting of the elements of $F''$ integral over the $R$-subalgebra $R[j''] =$ `Algebra.adjoin R {j''}`, and likewise $A =$ `chartAlgFin R F j` for the elements of $F$ integral over $R[j]$. The assertion is that there exists a ring homomorphism $\iota \colon A'' \to A$ with the following three properties: (i) $\iota$ is induced by $\varphi$, in the sense that for every $x \in A''$ the image of $\iota(x)$ in $F$ equals $\varphi(x)$; (ii) $\iota$ is an integral ring homomorphism, i.e. every element of $A$ is integral over $A''$ via $\iota$; and (iii) every $y \in A$ whose image in $F$ lies in the range of $\varphi$ is of the form $\iota(x)$ for some $x \in A''$. Thus $A \cap \varphi(F'') = \iota(A'')$ and $A$ is integral over this subring.
--
--   This records the functoriality of the finite chart of the two-chart integral model of a curve with coordinate $j$ in the field $F$: an $R$-algebra map of fields matching the coordinates induces a map of chart rings which is integral and whose image is exactly the part of the chart ring visible in the subfield. It is used in the analysis of maximal ideals of the finite chart ring at full level, where elements of a chart ring lying in a subfield must be recognised as coming from the corresponding smaller chart ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringHom_chartAlgFin_coe_eq_and_isIntegral_and_forall_exists_of_algHom
    (R : Type u) [CommRing R]
    (F'' : Type u) [Field F''] [Algebra R F''] (F : Type u) [Field F] [Algebra R F]
    (φ : F'' →ₐ[R] F)
    (j'' : F'') [Fact (j'' ≠ 0)] (j : F) [Fact (j ≠ 0)] (hφj : φ j'' = j) :
    ∃ ι : ↥(chartAlgFin R F'' j'') →+* ↥(chartAlgFin R F j),
      (∀ x : ↥(chartAlgFin R F'' j''), ((ι x : ↥(chartAlgFin R F j)) : F) = φ (x : F'')) ∧
      ι.IsIntegral ∧
      (∀ y : ↥(chartAlgFin R F j), (y : F) ∈ Set.range φ → ∃ x : ↥(chartAlgFin R F'' j''), ι x = y) := by sorry
