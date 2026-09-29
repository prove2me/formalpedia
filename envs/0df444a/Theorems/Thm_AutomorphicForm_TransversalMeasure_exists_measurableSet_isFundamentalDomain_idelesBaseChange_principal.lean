-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal
-- name    : AutomorphicForm.TransversalMeasure.exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/485c1a54-d24a-5d4d-8c5d-d125b63d80fa
-- title:
--   Measurable fundamental domain for the principal K-ideles in A_L^×
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, and equip the idele group $(\mathbb{A}_L)^\times$ of $L$ — the unit group of the adele ring `AdeleRing (𝓞 L) L` — with the Borel $\sigma$-algebra [`NumberField.Idele.ideleBorel`](def/NumberField_IdeleProductMeasure.html#L384) and the Haar measure [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391). Consider the group homomorphism $K^\times \to (\mathbb{A}_L)^\times$ obtained by composing the map on unit groups induced by the structure map $K \to \mathbb{A}_K$ with [`AutomorphicForm.TransversalMeasure.idelesBaseChange K L`](def/AutomorphicForm_TransversalMeasure.html#L85), the map on unit groups induced by the ring homomorphism [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14) from the adele ring of $K$ to the adele ring of $L$; let $G \le (\mathbb{A}_L)^\times$ denote the range of this composite, the image of the principal ideles of $K$ in the ideles of $L$. The assertion is that there exists a subset $\Omega \subseteq (\mathbb{A}_L)^\times$ which is measurable and which is a fundamental domain, in Mathlib's sense, for the multiplication action of $G$ on $(\mathbb{A}_L)^\times$ with respect to `idelicHaar L`: $\Omega$ is null measurable, its $G$-translates cover $(\mathbb{A}_L)^\times$ up to a null set, and distinct translates are almost everywhere disjoint.
--
--   This is the measure-theoretic input for integrating over the torus variable in the idelic theory: the usual fundamental domain of Tate's thesis for the principal ideles $L^\times$ is replaced by one for the smaller subgroup coming from $K^\times$ along base change. It is used in the analysis of the cuspidal kernel and its truncation for automorphic forms, where the unfolded integral runs over such a domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem AutomorphicForm.TransversalMeasure.exists_measurableSet_isFundamentalDomain_idelesBaseChange_principal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ Ω : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet Ω ∧
      IsFundamentalDomain
        ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
        (NumberField.Idele.idelicHaar L) := by sorry
