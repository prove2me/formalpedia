-- Prove2me | Theorems.Thm_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
-- name    : Algebra.card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6ae9acc3-83a7-5ad3-baf4-7b15e792d14d
-- title:
--   Counting 𝒪̂-embeddings of fixed slope into a valued field
-- statement:
--   Let $\hat{\mathcal O}$ be a discrete valuation ring which is a domain and is adically complete with respect to its maximal ideal, and let $\varpi \in \hat{\mathcal O}$ be irreducible. Let $S$ be a commutative $\hat{\mathcal O}$-algebra which is module-finite over $\hat{\mathcal O}$, let $x \in S$, and let $C$ be a field with an $\hat{\mathcal O}$-algebra structure carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two compatibility conditions: for $a \in \hat{\mathcal O}$ one has $v(a) < 1$ if and only if $a$ lies in the maximal ideal of $\hat{\mathcal O}$, and $v(a) = 0$ only for $a = 0$. Let $r \ge 1$ and $p$ be natural numbers, and let $\Phi$ be a finite set of $\hat{\mathcal O}$-algebra homomorphisms $\varphi : S \to C$ such that $v(\varphi x)^r = v(\varpi)^p$ for every $\varphi \in \Phi$. Then the cardinality of $\Phi$, viewed in $\mathbb N \cup \{\infty\}$, is at most the (finitely supported) sum of $\operatorname{finrank}_{\hat{\mathcal O}}(S/\mathfrak P)$ over those points $\mathfrak P$ of the prime spectrum of $S$ whose ideal is a minimal prime of $S$, does not contain the image of $\varpi$, and satisfies $r \cdot \operatorname{length}_{\hat{\mathcal O}}\bigl((S/\mathfrak P)/(\bar x)\bigr) = p \cdot \operatorname{finrank}_{\hat{\mathcal O}}(S/\mathfrak P)$ in $\mathbb N \cup \{\infty\}$, where $\bar x$ is the image of $x$ in $S/\mathfrak P$.
--
--   This is a slope-counting bound: embeddings of a module-finite algebra over a complete discrete valuation ring into a valued field are sorted according to the minimal prime they kill, and on each such branch the valuation of $\varphi x$ is determined by a length, so only branches of the prescribed slope $p/r$ contribute, each at most its $\hat{\mathcal O}$-rank. It is used to bound the number of prolongations in the place-specialisation arguments on modular curves, being cited by the two `ProlongationTuple` cardinality estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing

theorem Algebra.card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
    {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [IsAdicComplete (maximalIdeal Ô) Ô]
    (ϖ : Ô) (hϖ : Irreducible ϖ)
    (S : Type u) [CommRing S] [Algebra Ô S] [Module.Finite Ô S] (x : S)
    (C : Type v) [Field C] [Algebra Ô C]
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
    (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ maximalIdeal Ô)
    (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ)
    (Φ : Finset (S →ₐ[Ô] C)) (hΦ : ∀ φ ∈ Φ, v (φ x) ^ r = v (algebraMap Ô C ϖ) ^ p) :
    (Φ.card : ℕ∞) ≤
      ∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal ∧
          (r : ℕ∞) * Module.length Ô ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal x}) =
            ((p * Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ℕ∞) := by sorry
