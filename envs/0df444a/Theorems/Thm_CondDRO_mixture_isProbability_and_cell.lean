-- Prove2me | Theorems.Thm_CondDRO_mixture_isProbability_and_cell
-- name    : CondDRO.mixture_isProbability_and_cell
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:15.823982+00:00
-- url     : https://prove2.me/theorems/77ef5348-a825-4c86-b48d-823cc5fcb267
-- title:
--   p.10 on (2.9): every $Q\in\mathfrak M_\nu$ is a probability measure with $Q(\varpi_i)=\nu_i$
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space and $\{\varpi_i\}_{i\in\mathcal I}$ a finite partition of $\Omega$ into nonempty measurable sets. For each $i$ let $\mathfrak A_i$ be a set of probability measures on $(\Omega,\mathcal F)$ supported on $\varpi_i$, i.e. $Q(\Omega\setminus\varpi_i)=0$ for $Q\in\mathfrak A_i$. Let $\nu_i>0$ with $\sum_{i\in\mathcal I}\nu_i=1$, and let $\mathfrak M_\nu=\sum_i\nu_i\mathfrak A_i$ be the mixture (2.9). Then every $Q\in\mathfrak M_\nu$ is a probability measure and
--
--   $$
--   Q(\varpi_i)=\nu_i\qquad\text{for every }i\in\mathcal I .
--   $$
--
--   In particular every atom has positive probability under every member of $\mathfrak M_\nu$, so $\mathfrak M_\nu$ (when nonempty) satisfies Assumption 2.1. This is the paper's remark on p.10 that in (2.9) "the condition there that all probabilities $\nu_i$ are positive ensues that the support of the corresponding probability measure coincides with $\Omega_1$": in the §3 product-space setting the atoms are $\{\omega'\}\times\Omega_2$ and the marginal of $Q$ on the atoms is $\nu$.
--
--   **Formalization Note** "Supported on $\varpi_i$" is $Q(\varpi_i^{\mathrm c})=0$. The weights enter the sum of measures as `ENNReal.ofReal (ν i)`, and the conclusion $Q(\varpi_i)=\nu_i$ is stated in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: the remark on p.10 is phrased for the product space Ω₁ × Ω₂ of §3 (the support of the marginal of Q on Ω₁ is Ω₁) → Lean states it in the §2 setting of (2.9): Q(ϖᵢ) = νᵢ for every atom, and Q is a probability measure; reason: the remark compares (3.11) with (2.9), and with atoms {ω′} × Ω₂ the marginal of Q on Ω₁ is the vector (Q(ϖᵢ))ᵢ, so the remark says Q(ϖᵢ) = νᵢ > 0
--   - encoding: "supported on the set ϖᵢ" → Q (ϖ.cell i)ᶜ = 0; reason: the support condition the paper uses for P|ϖᵢ of (2.4)
--   - encoding: νᵢ Qᵢ → ENNReal.ofReal (ν i) • q i, Q(ϖᵢ) = νᵢ as ENNReal.ofReal (ν i); reason: Lean's measures take values in [0, ∞]; νᵢ > 0, so the same numbers
--   - generalization: the sets 𝔄ᵢ are nonempty (p.5, "(arbitrary, nonempty) sets 𝔄i") → nonemptiness not assumed; reason: if some 𝔄ᵢ is empty then 𝔐_ν is empty and the claim holds vacuously, so the statement specializes to the paper's
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), p.10, after (3.12) ("(3.11) defines the same set 𝔐ν as in (2.9) (the condition there that all probabilities νi are positive ensues that the support of the corresponding probability measure coincides with Ω1)"), applied to (2.9), p.5

import Mathlib
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_mixture

open MeasureTheory

namespace CondDRO

/-- **Every measure of the mixture 𝔐_ν is a probability measure whose mass on the atom ϖᵢ is νᵢ.**
Shapiro & Pichler, *Conditional Distributionally Robust Functionals*, preprint (October 9, 2022),
p.10, after (3.12): "(3.11) defines the same set 𝔐ν as in (2.9) (the condition there that all
probabilities νi are positive ensues that the support of the corresponding probability measure
coincides with Ω1)". In the §2 setting of (2.9), p.5: for a finite partition {ϖᵢ}, sets 𝔄ᵢ of
probability measures supported on ϖᵢ and positive probabilities νᵢ (Σνᵢ = 1), every
`Q ∈ 𝔐_ν = Σᵢ νᵢ 𝔄ᵢ` is a probability measure with `Q(ϖᵢ) = νᵢ` for all `i`; in particular 𝔐_ν
satisfies Assumption 2.1 (p.5).

**Formalization Note.** "Supported on ϖᵢ" is `Q (ϖ.cell i)ᶜ = 0`; `νᵢ` enters the sum of measures
as `ENNReal.ofReal (ν i)`. -/
theorem mixture_isProbability_and_cell {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_prob : ∀ i, ∀ Q ∈ A i, IsProbabilityMeasure Q)
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (hν_pos : ∀ i, 0 < ν i) (hν_sum : ∑ i, ν i = 1) :
    ∀ Q ∈ mixture A ν,
      IsProbabilityMeasure Q ∧ ∀ i, Q (ϖ.cell i) = ENNReal.ofReal (ν i) := by sorry

end CondDRO
