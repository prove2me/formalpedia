-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
-- name    : AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/9050e3de-11ca-5b82-b89e-b0bfdfbc32b9
-- title:
--   Order at infinity under reduction of E(X) to K(X)
-- statement:
--   Let $K$, $E$, $L$ be fields with $E$ an algebraically closed extension of $K$ and $L$ an extension of the rational function field $K(X)$. Let $A$ be a valuation subring of $E$ such that $\operatorname{image}(K) \subseteq A$ and such that every $a \in A$ satisfies $v_A(a - k) < 1$ for some $k \in K$ (so $K$ represents the residues of $A$). Let $O$ be a valuation subring of $E(X)$ and $\rho \colon O \to L$ a ring homomorphism such that: a constant $c \in E$ lies in $O$ exactly when $c \in A$; $\ker \rho$ is the maximal ideal of $O$; and for every $p \in K[X]$ the polynomial $p$, viewed in $E[X] \subseteq E(X)$, lies in $O$ and is sent by $\rho$ to the image in $L$ of $p$ viewed in $K(X)$. Let $G \in O$ and $N \in K(X)$ with $N \neq 0$ and $\rho(G)$ equal to the image of $N$ in $L$. Let $S$ be a finite subset of $E$ all of whose elements lie outside $A$ and which contains every $\beta \notin A$ with $\operatorname{ord}_{X = \beta}(G) \neq 0$. Then $$\operatorname{ord}_{\infty}(N) = \operatorname{ord}_{\infty}(G) + \sum_{\beta \in S} \operatorname{ord}_{X = \beta}(G),$$ where on the left the order is taken at the place of $K(X)/K$ given by the valuation subring of the infinite valuation, and on the right the orders are taken at the corresponding infinite place of $E(X)/E$ and at the places of $E(X)/E$ cut out by the irreducible polynomials $X - \beta$; in each case $\operatorname{ord}$ is minus the logarithm of the height-one-spectrum valuation attached to the place.
--
--   This is the computation, in Deuring's theory of reduction of function fields with respect to a place of the constant field, of the behaviour of the order at infinity: the places of $E(X)$ lying above the infinite place of the reduced field $K(X)$ are the infinite place together with the points $X = \beta$ with $\beta$ not integral at $A$. It is used in the verification that reduction of divisors along such a retraction preserves orders, in [`AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction`](thm.html#AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [IsAlgClosed E]
    [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)] [Algebra (RatFunc K) L]
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
    (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
        ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) := by sorry
