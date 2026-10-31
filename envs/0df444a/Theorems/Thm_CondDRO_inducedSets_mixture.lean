-- Prove2me | Theorems.Thm_CondDRO_inducedSets_mixture
-- name    : CondDRO.inducedSets_mixture
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:48.183997+00:00
-- url     : https://prove2.me/theorems/d923cabf-212d-4d6e-a1b0-cbd0c689572c
-- title:
--   p.5: for $\mathfrak M=\mathfrak M_\nu$ each $\mathfrak A_i$ coincides with the right-hand side of (2.8)
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space and $\{\varpi_i\}_{i\in\mathcal I}$ a finite partition of $\Omega$ into nonempty measurable sets. For each $i$ let $\mathfrak A_i$ be a **nonempty** set of probability measures supported on $\varpi_i$ ($Q(\Omega\setminus\varpi_i)=0$ for $Q\in\mathfrak A_i$). Let $\nu_i>0$ with $\sum_i\nu_i=1$ and $\mathfrak M_\nu=\sum_i\nu_i\mathfrak A_i$ (2.9). Then for every $i\in\mathcal I$
--
--   $$
--   \mathfrak A_i=\bigl\{\,Q_{|\varpi_i}\ :\ Q\in\mathfrak M_\nu\text{ and }Q(\varpi_i)\neq0\,\bigr\},
--   $$
--
--   where $Q_{|\varpi_i}(A)=Q(A\cap\varpi_i)/Q(\varpi_i)$ is the conditional probability (2.4). That is, the sets (2.8) induced by $\mathfrak M=\mathfrak M_\nu$ are the sets $\mathfrak A_i$ one started from.
--
--   This is the step that reduces Proposition 2.1 to the identity $\mathcal R_{|\mathcal G}=\mathcal R^\star_{|\mathcal G}$ for induced sets (2.8).
--
--   **Formalization Note** $Q_{|\varpi_i}$ is Mathlib's `ProbabilityTheory.cond`; the weights enter (2.9) as `ENNReal.ofReal (ν i)`.
--
--   Differences from the source:
--   - encoding: "supported on the set ϖᵢ" → Q (ϖ.cell i)ᶜ = 0; reason: the support condition the paper uses for P|ϖᵢ of (2.4)
--   - encoding: Q|ϖᵢ of (2.4) → ProbabilityTheory.cond Q (ϖ.cell i) = (Q ϖᵢ)⁻¹ • Q.restrict ϖᵢ; reason: equal to (2.4) for a probability measure with Q(ϖᵢ) ≠ 0, the only case (2.8) uses
--   - encoding: νᵢ Qᵢ → ENNReal.ofReal (ν i) • q i; reason: Lean's measures take scalars in [0, ∞]; νᵢ > 0, so the same measures
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), p.5, after (2.9) ("For such set 𝔐 = 𝔐ν we have that each 𝔄i coincides with the right-hand side of (2.8)")

import Mathlib
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_inducedSets
import Definitions.Def_CondDRO_mixture

open MeasureTheory

namespace CondDRO

/-- **For 𝔐 = 𝔐_ν, the sets (2.8) give back the 𝔄ᵢ.** Shapiro & Pichler, *Conditional
Distributionally Robust Functionals*, preprint (October 9, 2022), p.5: "For such set 𝔐 = 𝔐ν we
have that each 𝔄i coincides with the right-hand side of (2.8)." For a finite partition {ϖᵢ},
nonempty sets 𝔄ᵢ of probability measures supported on ϖᵢ, and positive probabilities νᵢ
(Σνᵢ = 1): `𝔄ᵢ = { Q|ϖᵢ | Q ∈ 𝔐_ν and Q(ϖᵢ) ≠ 0 }` for every `i`.

**Formalization Note.** "Supported on ϖᵢ" is `Q (ϖ.cell i)ᶜ = 0`; `Q|ϖᵢ` is Mathlib's
`ProbabilityTheory.cond` (see `inducedSets`); `νᵢ` enters (2.9) as `ENNReal.ofReal (ν i)`. -/
theorem inducedSets_mixture {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_ne : ∀ i, (A i).Nonempty)
    (hA_prob : ∀ i, ∀ Q ∈ A i, IsProbabilityMeasure Q)
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (hν_pos : ∀ i, 0 < ν i) (hν_sum : ∑ i, ν i = 1) :
    ∀ i, inducedSets (mixture A ν) ϖ i = A i := by sorry

end CondDRO
