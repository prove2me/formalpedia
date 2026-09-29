-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/1377e03d-608b-5d91-afca-94d007a0aa0e
-- title:
--   Finite chart of a base-changed two-chart integral model
-- statement:
--   Fix a universe $u$ and let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, $j \in F$ a nonzero element, and $O$ a commutative $R$-algebra, all of type in universe $u$. Write $A :=$ `chartAlgFin R F j` for the $R$-subalgebra of $F$ consisting of the elements of $F$ integral over the subalgebra $R[j] =$ `Algebra.adjoin R {j}`, and let `toBase R F j` be the structure morphism from the two-chart integral model $X$ (the pushout of `fFin R F j` and `fInf R F j`) to $\operatorname{Spec} R$, obtained by descending the morphisms induced by $R \to A$ and $R \to$ `chartAlgInf R F j`. The assertion is that there exists a morphism of schemes $g : \operatorname{Spec}(A \otimes_R O) \to X \times_{\operatorname{Spec} R} \operatorname{Spec} O$, the pullback of `toBase R F j` along the morphism $\operatorname{Spec} O \to \operatorname{Spec} R$ induced by $R \to O$, such that: $g$ is an open immersion; $g$ followed by the first projection equals $\operatorname{Spec}$ of $a \mapsto a \otimes 1$ followed by the finite-chart morphism `ιFin R F j`; $g$ followed by the second projection equals $\operatorname{Spec}$ of $o \mapsto 1 \otimes o$; and the range of the underlying continuous map of $g$ is, as a subset of the pullback, the preimage under the first projection of the open image of `ιFin R F j` on the whole of $\operatorname{Spec} A$.
--
--   This identifies the finite chart of the base change to $O$ of the two-chart integral model with the spectrum of $A \otimes_R O$, compatibly with both projections and with the expected open image. It is used by the consumers that compute local rings and stalk maps of the base-changed model over the finite chart, including the statements on stalks at generic points and on the Dedekind property of quotients of the finite chart algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
universe u
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [Algebra R O] :
    ∃ g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j)) (B := O))) ≫
          ιFin R F j ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := O)).toRingHom) ∧
      Set.range g.base = ((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤) :
        Set ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))))) := by sorry
