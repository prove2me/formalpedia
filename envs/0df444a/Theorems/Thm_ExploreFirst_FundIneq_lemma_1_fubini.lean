-- Prove2me | Theorems.Thm_ExploreFirst_FundIneq_lemma_1_fubini
-- name    : ExploreFirst.FundIneq.lemma_1_fubini
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:51.211564+00:00
-- url     : https://prove2.me/theorems/93081dab-2c53-44da-b033-6574d7ee7bab
-- title:
--   Lemma 1 proof, p. 8 — (ℙ ⊗ λ){(γ, x) : x ≤ Z(γ)} = 𝔼[Z] for Z with values in [0, 1]
-- statement:
--   Let $(\Gamma,\mathcal G)$ be a measurable space with a probability measure $\mathbb P$, let $\lambda$ be the Lebesgue measure on $[0,1]$, and let $Z:\Gamma\to[0,1]$ be measurable. Consider the event
--   $$
--   E=\{(\gamma,x)\in\Gamma\times[0,1]:\ x\le Z(\gamma)\}.
--   $$
--   Then
--   $$
--   (\mathbb P\otimes\lambda)(E)=\int_\Gamma Z(\gamma)\,\mathrm d\mathbb P(\gamma)=\mathbb E[Z].
--   $$
--
--   This is the last step of the proof of Lemma 1: it identifies the parameter of the Bernoulli law of $\mathbb I_E$ with the expectation of $Z$, which turns the event inequality into Lemma 1.
--
--   **Formalization Note.** $Z$ is a real-valued measurable function with values in $[0,1]$; $\lambda$ is the canonical volume on Mathlib's `unitInterval`. The paper writes the integral over $\Omega$; the integration domain is $\Gamma$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 8, proof of Lemma 1, last display

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- Garivier, Ménard, Stoltz, arXiv:1602.07182v3, p. 8, proof of Lemma 1, last display: for a
measurable `Z : Γ → [0, 1]` and `E = {(γ, x) ∈ Γ × [0, 1] : x ≤ Z(γ)}`,
`(ℙ ⊗ λ)(E) = 𝔼[Z]`, with `λ` the Lebesgue measure on the unit interval. -/
theorem lemma_1_fubini {Γ : Type*} [MeasurableSpace Γ] (P : Measure Γ) [IsProbabilityMeasure P]
    (Z : Γ → ℝ) (hZ : Measurable Z) (hZ01 : ∀ γ, Z γ ∈ Set.Icc (0 : ℝ) 1) :
    (P.prod (volume : Measure unitInterval)).real {p | (p.2 : ℝ) ≤ Z p.1} = ∫ γ, Z γ ∂P := by sorry

end ExploreFirst.FundIneq
