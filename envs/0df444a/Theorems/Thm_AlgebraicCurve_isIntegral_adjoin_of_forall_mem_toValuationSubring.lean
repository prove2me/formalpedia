-- Prove2me | Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
-- name    : AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ec854fae-ead3-5215-b9ae-f4ef7f1f629d
-- title:
--   Integrality over K[t] from membership in all places containing t
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose there is an element $x \in F$ such that $F$ is finite-dimensional and separable over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $t, z \in F$, and assume that for every place $v$ of $F$ over $K$ — that is, for every structure consisting of a valuation subring $\mathcal{O}_v \subseteq F$ which contains $\mathrm{algebraMap}\,K\,F\,a$ for all $a \in K$, is not the whole of $F$, and is a principal ideal ring — the implication $t \in \mathcal{O}_v \Rightarrow z \in \mathcal{O}_v$ holds. Then $z$ is integral over the $K$-subalgebra $K[t] =$ `Algebra.adjoin K {t}` of $F$, i.e. $z$ satisfies a monic polynomial with coefficients in $K[t]$. No hypothesis on the characteristic of $K$ is imposed, and the hypothesis on places is phrased by membership in the valuation subrings rather than by inequalities between valuations.
--
--   This is the standard characterisation of the integral closure of $K[t]$ in a function field as the intersection of the valuation rings of the places at which $t$ is regular, in the form needed for the project's theory of algebraic curves. It is used in the construction of regular prolongations and in the characteristic-$p$ models of modular curves, where integrality over a coordinate ring must be deduced from local regularity at all places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (t z : F)
    (h : ∀ v : AlgebraicCurve.Place K F, t ∈ v.toValuationSubring → z ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by sorry
