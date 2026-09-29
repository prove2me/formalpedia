-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
-- name    : AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c2700d3f-c07d-5588-8b25-09576fc6b229
-- title:
--   Pullback of a proper valuation subring is a place
-- statement:
--   Let $K$, $F$ and $F'$ be fields with $F$ a $K$-algebra, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}` and the extension $F/K(x)$ is separable. Let $\varphi \colon F \to F'$ be a ring homomorphism, and let $w$ be a valuation subring of $F'$. Assume that $\varphi(a)$ lies in $w$ for every $a$ in the image of $K$ in $F$ under the structure map, and that $\varphi(y) \notin w$ for at least one $y \in F$. Then there is a place $v$ of $F/K$, that is, a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, different from all of $F$, and whose underlying ring is a principal ideal ring, such that $\mathcal{O}_v$ is exactly the preimage $\varphi^{-1}(w)$ of $w$ under $\varphi$.
--
--   This is the standard construction of a place of a one-variable function field $F/K$ by pulling back a proper valuation subring along a homomorphism out of $F$, here with separability of $F$ over $K(x)$ assumed in place of any hypothesis on the characteristic; the separability is what makes the integral closure in $F$ of the valuation ring of the corresponding place of $K(x)$ a finite module, hence Dedekind. It is used to produce places of $F/K$ with prescribed behaviour, for instance in the results on places obtained from $K$-algebra homomorphisms and on constant field extensions, including the case of algebraically closed constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →+* F') (w : ValuationSubring F')
    (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by sorry
