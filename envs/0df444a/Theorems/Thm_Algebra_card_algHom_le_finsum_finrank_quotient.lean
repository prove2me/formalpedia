-- Prove2me | Theorems.Thm_Algebra_card_algHom_le_finsum_finrank_quotient
-- name    : Algebra.card_algHom_le_finsum_finrank_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/4741ad6e-a111-522b-b1a3-b0ea94e760ec
-- title:
--   Counting algebra maps into a field by branch ranks
-- statement:
--   Let $\hat{\mathcal O}$ be a commutative ring which is a domain and a discrete valuation ring, and let $\varpi \in \hat{\mathcal O}$ be a nonzero element (no further condition, such as being a uniformiser or a non-unit, is imposed). Let $S$ be a commutative $\hat{\mathcal O}$-algebra which is finite as an $\hat{\mathcal O}$-module, and let $C$ be a field equipped with an $\hat{\mathcal O}$-algebra structure whose structure map $\hat{\mathcal O} \to C$ is injective. Let $\Phi$ be a finite set of $\hat{\mathcal O}$-algebra homomorphisms $S \to C$. Then, as an inequality in $\mathbb N \cup \{\infty\}$, the cardinality of $\Phi$ is at most $$\sum_{\mathfrak P} \operatorname{finrank}_{\hat{\mathcal O}}\bigl(S/\mathfrak P\bigr),$$ the sum being taken over those points $\mathfrak P$ of the prime spectrum of $S$ whose underlying ideal is a minimal prime of $S$ and does not contain the image of $\varpi$ in $S$. The right-hand side is a `finsum`, so each admissible $\mathfrak P$ contributes the $\hat{\mathcal O}$-rank of the quotient $S/\mathfrak P$ (with Mathlib's convention that `Module.finrank` is $0$ when no finite rank exists) and all other points contribute $0$.
--
--   This is a branch-counting bound in the style of Dedekind's independence of characters: each $\hat{\mathcal O}$-algebra map $S \to C$ kills a minimal prime avoiding $\varpi$, and on each such branch the number of maps is bounded by the rank of the branch over $\hat{\mathcal O}$. It is used in the analysis of places of modular curves, where it bounds the number of prolongations with a prescribed evaluation kernel by the total rank of the relevant branches.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_card_algHom_le_finsum_finrank_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Algebra.card_algHom_le_finsum_finrank_quotient
    {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
    (ϖ : Ô) (hϖ0 : ϖ ≠ 0)
    (S : Type u) [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
    (C : Type v) [Field C] [Algebra Ô C] (hinj : Function.Injective (algebraMap Ô C))
    (Φ : Finset (S →ₐ[Ô] C)) :
    (Φ.card : ℕ∞) ≤
      ∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal),
        (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞) := by sorry
