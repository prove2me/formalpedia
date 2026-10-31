-- Prove2me | Theorems.Thm_CondDRO_condRM_inducedSets_eq_condDRF
-- name    : CondDRO.condRM_inducedSets_eq_condDRF
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:59.821984+00:00
-- url     : https://prove2.me/theorems/1d53af94-f270-413e-8572-f7706616955c
-- title:
--   p.5: for the sets (2.8) of $\mathfrak M$, $\mathcal R_{|\mathcal G}(\cdot)=\mathcal R^\star_{|\mathcal G}(\cdot)$
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space, $\{\varpi_i\}_{i\in\mathcal I}$ a finite partition of $\Omega$ into nonempty measurable sets generating $\mathcal G$, and $\mathfrak M$ a set of probability measures satisfying **Assumption 2.1**: for every $i\in\mathcal I$ there is $Q\in\mathfrak M$ with $Q(\varpi_i)\neq0$. Let $\mathfrak A_i=\{Q_{|\varpi_i}: Q\in\mathfrak M,\ Q(\varpi_i)\neq0\}$ be the induced sets (2.8), and let $Z:\Omega\to\mathbb R$ be measurable and integrable with respect to every $Q\in\mathfrak M$. Then for every $i\in\mathcal I$
--
--   $$
--   \mathcal R_{|\mathcal G}(Z)(\varpi_i)=\sup_{Q\in\mathfrak A_i}\mathbb E_Q[Z]=\sup_{Q\in\mathfrak M,\;Q(\varpi_i)\neq0}\frac{1}{Q(\varpi_i)}\int_{\varpi_i}Z\,dQ=\mathcal R^\star_{|\mathcal G}(Z)(\varpi_i),
--   $$
--
--   that is, the conditional risk measure (2.7) of the induced sets equals the conditional distributionally robust functional (2.6) of $\mathfrak M$.
--
--   **Formalization Note** Both functionals take values in the extended reals, atom by atom.
--
--   Differences from the source:
--   - generalization: R(Z) is assumed finite valued (p.3) and the functionals map into ℝ → values in EReal, no finiteness assumption; reason: whenever the paper's finiteness assumption holds both sides are the same real numbers, so the statement specializes to the paper's
--   - reading: Z ∈ 𝒵, "an appropriate linear space of measurable variables" with E_Q[Z] well-defined for every Q ∈ 𝔐 (p.3) → Measurable Z and Integrable Z Q for every Q ∈ 𝔐; reason: the paper's standing requirement, made precise
--   - encoding: a 𝒢-measurable variable constant on each atom → a function I → EReal (its value on each atom); reason: the paper's notation Z(ϖᵢ) of (2.3); the same objects
--   - encoding: Q|ϖᵢ of (2.4) → ProbabilityTheory.cond Q (ϖ.cell i); reason: equal to (2.4) for a probability measure with Q(ϖᵢ) ≠ 0, the only case (2.8) uses
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), p.5, after (2.8) ("For sets 𝔄i defined in (2.8), R|𝒢(ϖi) can be written as the supremum in the right-hand side of (2.6), that is for such sets R|𝒢(·) = R⋆|𝒢(·)"); Assumption 2.1, p.5

import Mathlib
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_condDRF
import Definitions.Def_CondDRO_condRM
import Definitions.Def_CondDRO_inducedSets

open MeasureTheory

namespace CondDRO

/-- **For the sets (2.8) of an ambiguity set 𝔐, R|𝒢 = R⋆|𝒢.** Shapiro & Pichler, *Conditional
Distributionally Robust Functionals*, preprint (October 9, 2022), p.5: "For sets 𝔄i defined in
(2.8), R|𝒢(ϖi) can be written as the supremum in the right-hand side of (2.6), that is for such
sets R|𝒢(·) = R⋆|𝒢(·)." For a finite partition {ϖᵢ}, a set 𝔐 of probability measures satisfying
Assumption 2.1 (p.5: for every `i` there is `Q ∈ 𝔐` with `Q(ϖᵢ) ≠ 0`), and a measurable `Z`
integrable for every `Q ∈ 𝔐`: the conditional risk measure (2.7) of the sets (2.8) equals the
conditional distributionally robust functional (2.6) of 𝔐, on every atom.

**Formalization Note.** Both functionals take values in `EReal` (see `condDRF`, `condRM`); the
paper's standing assumption that R(Z) is finite is not imposed. -/
theorem condRM_inducedSets_eq_condDRF {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (M : Set (Measure Ω))
    (hM_prob : ∀ Q ∈ M, IsProbabilityMeasure Q)
    (hM_assum : ∀ i, ∃ Q ∈ M, Q (ϖ.cell i) ≠ 0)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z) (hZ_int : ∀ Q ∈ M, Integrable Z Q) :
    condRM (inducedSets M ϖ) Z = condDRF M ϖ Z := by sorry

end CondDRO
