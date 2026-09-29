-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_act_add_mul_zsmul_neg_pointCommGroup
-- name    : CerednikDrinfeld.QM.act_add_mul_zsmul_neg_pointCommGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b8c9452c-aa84-552d-ba57-9bde983e82ef
-- title:
--   Quaternion order action read in the endomorphism group
-- statement:
--   Let $K$ be a field, $f : A \to \operatorname{Spec} K$ a scheme over $K$, and $L$ a relative group law on $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws and naturality in the test scheme) on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} K$; assume $L$ commutative ($hc$). Let $a,b \in \mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order, i.e. an order contained in no strictly larger order. Let $\mathrm{act} : \Lambda \to (A \to A)$ assign to each $x$ an endomorphism with $\mathrm{act}\,x$ followed by $f$ equal to $f$, and assume: each $\mathrm{act}\,x$ carries $T$-points to $T$-points compatibly with the group law ($P \mapsto P$ followed by $\mathrm{act}\,x$ is a homomorphism for $L$); $\mathrm{act}\,1 = \mathrm{id}_A$; $\mathrm{act}(xy) = \mathrm{act}\,y$ followed by $\mathrm{act}\,x$ whenever $xy \in \Lambda$; and $\mathrm{act}(x+y)$ acts on each $T$-point as the $L$-product of the actions of $x$ and of $y$. Then, with $\mathrm{SchemeHomOver}\,f\,f$ given the commutative group structure coming from $L$, writing $\underline{\mathrm{act}}(x) = (\mathrm{act}\,x, \cdot)$: (1) $\underline{\mathrm{act}}(x+y) = \underline{\mathrm{act}}(x)\,\underline{\mathrm{act}}(y)$; (2) $\underline{\mathrm{act}}(xy)$ is $\underline{\mathrm{act}}(y)$ followed by $\underline{\mathrm{act}}(x)$, for $xy \in \Lambda$; (3) $\underline{\mathrm{act}}(k \cdot 1) = \mathrm{idPoint}^{k}$ for all $k \in \mathbb{Z}$; (4) $\underline{\mathrm{act}}(-x) = \underline{\mathrm{act}}(x)^{-1}$; (5) for all $T$-points $P,Q$, composing the $L$-product of $P$ and $Q$ with $\underline{\mathrm{act}}(x)$ gives the $L$-product of the two composites.
--
--   This is the dictionary translating the axioms of a quaternionic multiplication on an abelian scheme over $K$ into statements about the commutative group $\operatorname{End}$-like object $\mathrm{SchemeHomOver}\,f\,f$ under the relative group law: additivity becomes multiplicativity, the order multiplication becomes composition (in the opposite order), integers act as powers of the identity point, and negatives as inverses. It is used in the analysis of the action of a maximal order on the Jacobians in the Čerednik–Drinfeld setting, notably for the finiteness and rank computation for kernels of $\mathrm{act}\,x$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_act_add_mul_zsmul_neg_pointCommGroup.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.act_add_mul_zsmul_neg_pointCommGroup
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) :
    letI := L.pointCommGroup hc f
    (∀ x y : ↥Λ, (⟨act (x + y), act_over (x + y)⟩ : SchemeHomOver f f) = ⟨act x, act_over x⟩ * ⟨act y, act_over y⟩) ∧
    (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      (⟨act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩, act_over _⟩ : SchemeHomOver f f) =
        NeronModelInfra.schemeHomOverComp (⟨act y, act_over y⟩ : SchemeHomOver f f) ⟨act x, act_over x⟩) ∧
    (∀ k : ℤ, (⟨act (k • ⟨1, hΛ.isOrder.one_mem⟩), act_over _⟩ : SchemeHomOver f f) =
        (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ k) ∧
    (∀ x : ↥Λ, (⟨act (-x), act_over (-x)⟩ : SchemeHomOver f f) = (⟨act x, act_over x⟩ : SchemeHomOver f f)⁻¹) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t P Q) (⟨act x, act_over x⟩ : SchemeHomOver f f) =
        L.mul t (NeronModelInfra.schemeHomOverComp P ⟨act x, act_over x⟩)
          (NeronModelInfra.schemeHomOverComp Q ⟨act x, act_over x⟩)) := by sorry
