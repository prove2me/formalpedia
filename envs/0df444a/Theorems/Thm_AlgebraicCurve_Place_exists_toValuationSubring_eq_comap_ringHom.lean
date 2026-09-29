-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
-- name    : AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/de86ea3a-1842-5dc1-9167-e8f8988b4084
-- title:
--   Pullback of a valuation subring along φ gives a place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ a $K$-algebra and $\operatorname{char} K = 0$, and suppose there is an element $x \in F$ such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $\varphi : F \to F'$ be a ring homomorphism and let $w$ be a valuation subring of $F'$. Assume that $\varphi$ carries the image of $K$ into $w$, i.e. $\varphi(\mathrm{alg}_{K\to F}(a)) \in w$ for every $a \in K$, and that $w$ does not swallow all of $\varphi(F)$, i.e. there exists $y \in F$ with $\varphi(y) \notin w$. The conclusion is that there exists a place $v$ of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) — a valuation subring of $F$ which contains $\mathrm{alg}_{K\to F}(a)$ for all $a \in K$, is not the whole of $F$, and is a principal ideal ring — whose underlying valuation subring is exactly the preimage $\varphi^{-1}(w) =$ `w.comap φ`.
--
--   This is the construction of the place of $F/K$ lying under a given valuation of an extension or base change of $F$: the preimage of $w$ is a valuation subring of $F$, and the two hypotheses supply respectively the containment of $K$ and the properness needed for it to be a place, while finiteness of $F$ over a rational subfield $K(x)$ in characteristic zero gives the discreteness (principality). It is used in the divisor and differential theory of function fields, for instance in comparing divisors and orders under constant field extension and in the residue sum formula for differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (φ : F →+* F') (w : ValuationSubring F') (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by sorry
