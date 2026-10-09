-- Prove2me | Theorems.Thm_ExploreFirst_FundIneq_lemma_1_event
-- name    : ExploreFirst.FundIneq.lemma_1_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:57.785783+00:00
-- url     : https://prove2.me/theorems/43d624ea-121a-4d37-bc26-e6792f53d6dd
-- title:
--   Lemma 1 proof, p. 8 — KL(ℙ₁, ℙ₂) ≥ kl((ℙ₁ ⊗ λ)(E), (ℙ₂ ⊗ λ)(E)) for every event E of Γ × [0, 1]
-- statement:
--   Let $(\Gamma,\mathcal G)$ be a measurable space carrying two probability measures $\mathbb P_1$ and $\mathbb P_2$, let $\lambda$ be the Lebesgue measure on $[0,1]$, and let $E\in\mathcal G\otimes\mathcal B([0,1])$ be any measurable subset of $\Gamma\times[0,1]$. Write $\mathrm{kl}(p,q)$ for the Kullback–Leibler divergence between the Bernoulli distributions of parameters $p$ and $q$, with values in $[0,+\infty]$. Then
--   $$
--   \mathrm{KL}(\mathbb P_1,\mathbb P_2)\ \ge\ \mathrm{kl}\big((\mathbb P_1\otimes\lambda)(E),\ (\mathbb P_2\otimes\lambda)(E)\big).
--   $$
--
--   In the paper this display combines the tensorization equality $\mathrm{KL}(\mathbb P_1,\mathbb P_2)=\mathrm{KL}(\mathbb P_1\otimes\lambda,\mathbb P_2\otimes\lambda)$ with the data-processing inequality applied to the indicator $\mathbb I_E$, whose law under $\mathbb P_j\otimes\lambda$ is the Bernoulli distribution of parameter $(\mathbb P_j\otimes\lambda)(E)$.
--
--   **Formalization Note.** The statement is written, as on the page, for the product measures $\mathbb P_j\otimes\lambda$ on $\Gamma\times[0,1]$, with $\lambda$ the canonical volume on Mathlib's `unitInterval`. The binary divergence is the $[0,+\infty]$-valued `klBer` of the mission's definitions file.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 8, proof of Lemma 1, second display

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- Garivier, Ménard, Stoltz, arXiv:1602.07182v3, p. 8, proof of Lemma 1, second display: for every
event `E` of the product σ-algebra on `Γ × [0, 1]`,
`KL(ℙ₁, ℙ₂) ≥ kl((ℙ₁ ⊗ λ)(E), (ℙ₂ ⊗ λ)(E))`, with `λ` the Lebesgue measure on the unit interval. -/
theorem lemma_1_event {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (E : Set (Γ × unitInterval)) (hE : MeasurableSet E) :
    klBer ((P₁.prod (volume : Measure unitInterval)).real E)
        ((P₂.prod (volume : Measure unitInterval)).real E) ≤ klDiv P₁ P₂ := by sorry

end ExploreFirst.FundIneq
