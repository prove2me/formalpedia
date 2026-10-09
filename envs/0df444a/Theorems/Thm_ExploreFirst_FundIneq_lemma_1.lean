-- Prove2me | Theorems.Thm_ExploreFirst_FundIneq_lemma_1
-- name    : ExploreFirst.FundIneq.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:38.395351+00:00
-- url     : https://prove2.me/theorems/f03e2ad1-abe8-4ee8-a6d9-352221eb3354
-- title:
--   Lemma 1, p. 8 — KL(ℙ₁, ℙ₂) ≥ kl(𝔼₁[Z], 𝔼₂[Z]) for every measurable Z with values in [0, 1]
-- statement:
--   Let $(\Gamma,\mathcal G)$ be a measurable space equipped with two probability measures $\mathbb P_1$ and $\mathbb P_2$, with expectations $\mathbb E_1$ and $\mathbb E_2$, and let $Z:\Gamma\to[0,1]$ be a $\mathcal G$-measurable random variable. Write $\mathrm{kl}(p,q)$ for the Kullback–Leibler divergence between the Bernoulli distributions of parameters $p$ and $q$, with values in $[0,+\infty]$. Then
--   $$
--   \mathrm{KL}(\mathbb P_1,\mathbb P_2)\ \ge\ \mathrm{kl}\big(\mathbb E_1[Z],\ \mathbb E_2[Z]\big).
--   $$
--
--   Lemma 1 is the inequality half of (8). Applied to the laws of the full information $I_T$ under two bandit problems, and combined with the divergence decomposition, it gives the fundamental inequality (6). It extends the data-processing inequality from indicators of events to arbitrary $[0,1]$-valued statistics.
--
--   **Formalization Note.** The paper writes "$Z:\Omega\to[0,1]$"; the domain is $\Gamma$. $Z$ is a real-valued measurable function with values in $[0,1]$, and the paper's "distributions" are probability measures. Both sides take values in $[0,+\infty]$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 8, Lemma 1

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- Garivier, Ménard, Stoltz, arXiv:1602.07182v3, p. 8, Lemma 1: for two probability measures
`ℙ₁, ℙ₂` on a measurable space `Γ` and any measurable `Z : Γ → [0, 1]`,
`KL(ℙ₁, ℙ₂) ≥ kl(𝔼₁[Z], 𝔼₂[Z])`. -/
theorem lemma_1 {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (Z : Γ → ℝ) (hZ : Measurable Z) (hZ01 : ∀ γ, Z γ ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ γ, Z γ ∂P₁) (∫ γ, Z γ ∂P₂) ≤ klDiv P₁ P₂ := by sorry

end ExploreFirst.FundIneq
