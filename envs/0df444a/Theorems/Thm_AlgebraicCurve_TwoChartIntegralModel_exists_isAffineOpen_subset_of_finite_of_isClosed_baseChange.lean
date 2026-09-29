-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/edeb858b-71e6-5474-8df3-5f99cf527167
-- title:
--   Finite sets of the base change lie in one affine open
-- statement:
--   Fix a commutative ring $R$, a field $F$ with an $R$-algebra structure, and an element $j \in F$ with $j \neq 0$. Write $X =$ `TwoChartIntegralModel R F j` for the pushout in schemes of the two morphisms `fFin R F j` and `fInf R F j`, i.e. of the maps obtained by applying $\operatorname{Spec}$ to the inclusions `inclFin` and `inclInf` of the subalgebras `chartAlgFin R F j` $=$ `chartAlg R F {j}` and `chartAlgInf R F j` $=$ `chartAlg R F {j⁻¹}` of $F$ into the algebra underlying `XMid R F j`, and let `toBase R F j` $\colon X \to \operatorname{Spec} R$ be the morphism obtained from the pushout by descending the two structure morphisms $\operatorname{Spec}$ of $R \to$ `chartAlgFin R F j` and of $R \to$ `chartAlgInf R F j`. Let $A$ be a commutative local ring whose residue field is infinite, and $\varphi \colon R \to A$ a ring homomorphism. Let $T$ be a subset of the underlying topological space of the pullback of `toBase R F j` along $\operatorname{Spec}(\varphi)$; assume $T$ is finite and that each $t \in T$ is a closed point. Then there is an open subscheme $U$ of that pullback which is an affine open and contains $T$. The proof uses neither the closedness hypothesis on the points of $T$, nor the locality of $A$, nor the infinitude of its residue field.
--
--   This is the base-changed form of the statement that finitely many points of the two-chart integral model of $(R,F,j)$ can be enclosed in a single affine open, the standard device for replacing a non-affine curve model by an affine one near a finite set of points. It is used in the construction of invertible presentations framing the slope law for the model of the modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
    {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {A : Type u} [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] (φ : R →+* A)
    (T : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))
    (hT : T.Finite) (hTcl : ∀ t ∈ T, IsClosed ({t} : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))) :
    ∃ U : (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))).Opens,
      IsAffineOpen U ∧ T ⊆ (U : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ)))) := by sorry
