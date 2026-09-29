-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
-- name    : AlgebraicCurve.Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6ede62c6-10c0-5de5-b56a-b53aa6322115
-- title:
--   Embeddings inducing a given place counted by the ramification index
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $F$, $F'$ be $K$-algebras that are fields satisfying `IsCurveOver K F` and `IsCurveOver K F'`: every nonzero element has a principal divisor of degree zero, every place has residue field finite-dimensional over $K$, and the module of Kähler differentials $\Omega_{F/K}$ (respectively $\Omega_{F'/K}$) is free of rank one. Here a place of $F$ over $K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring homomorphism is integral, and assume `FiniteAlong K φ`, i.e. $F'$ is a finite module over $F$ through $\varphi$. Let $E$ be an algebraically closed field that is a $K$-algebra, $A \subseteq E$ a valuation subring, $e : F \to E$ a $K$-algebra map, and $v_0$ a place of $F$ with $f \in \mathcal{O}_{v_0} \iff e(f) \in A$ for all $f \in F$. Let $q$ be a place of $F'$ whose restriction along $\varphi$ is $v_0$, that is, $\varphi^{-1}(\mathcal{O}_q) = \mathcal{O}_{v_0}$. Then the set of $K$-algebra maps $\sigma : F' \to E$ with $\varphi$ followed by $\sigma$ equal to $e$ and $g \in \mathcal{O}_q \iff \sigma(g) \in A$ for all $g \in F'$ has cardinality (as a natural number, $0$ for an infinite set) equal to the ramification index of $q$ along $\varphi$, defined as the least positive integer of the form $\operatorname{ord}_q(\varphi(f))$ for some nonzero $f \in F$.
--
--   This is the classical count of the extensions of a place through embeddings into an algebraically closed valued field: since all residue fields here are $K$ itself, the residue degree is $1$ and each place $q$ of $F'$ above $v_0$ is induced by exactly $e(q/v_0)$ embeddings of $F'$ into $(E,A)$ extending $e$. It is used in the construction of the divisor correspondence attached to $\varphi$, in [`AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence`](thm.html#AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (A : ValuationSubring E) (e : F →ₐ[K] E) (v₀ : Place K F)
    (hev₀ : ∀ f : F, f ∈ v₀.toValuationSubring ↔ e f ∈ A)
    (q : Place K F') (hq : q.restrictAlong φ hφ = v₀) :
    Set.ncard {σ : F' →ₐ[K] E | σ.comp φ = e ∧
        ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      q.ramificationIndexAlong φ := by sorry
