-- Prove2me | Theorems.Thm_ExploreFirst_FundIneq_lemma_1_product
-- name    : ExploreFirst.FundIneq.lemma_1_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:46.48969+00:00
-- url     : https://prove2.me/theorems/ea9327a6-600a-420d-afa0-de346c78ff69
-- title:
--   Lemma 1 proof, p. 8 — augmenting by an independent uniform variable: KL(ℙ₁, ℙ₂) = KL(ℙ₁ ⊗ λ, ℙ₂ ⊗ λ)
-- statement:
--   Let $(\Gamma,\mathcal G)$ be a measurable space carrying two probability measures $\mathbb P_1$ and $\mathbb P_2$, and let $\lambda$ be the Lebesgue measure on $[0,1]$ with its Borel $\sigma$-algebra. Then the Kullback–Leibler divergence is unchanged when both measures are tensorized with $\lambda$:
--   $$
--   \mathrm{KL}(\mathbb P_1,\mathbb P_2)=\mathrm{KL}(\mathbb P_1\otimes\lambda,\ \mathbb P_2\otimes\lambda),
--   $$
--   as an identity in $[0,+\infty]$ (both sides may be $+\infty$).
--
--   This is the first step of the proof of Lemma 1: it enlarges the probability space by an independent uniform variable, so that a $[0,1]$-valued random variable $Z$ can be replaced by the indicator of the event $\{x\le Z(\gamma)\}$.
--
--   **Formalization Note.** The Lebesgue measure on $[0,1]$ is the canonical volume on Mathlib's unit interval `unitInterval`, a probability measure. The paper's "distributions" are probability measures.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 8, proof of Lemma 1, first display (the equality)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- Garivier, Ménard, Stoltz, arXiv:1602.07182v3, p. 8, proof of Lemma 1, first display (equality):
augmenting a probability space by an independent uniform variable on `[0, 1]` does not change the
Kullback–Leibler divergence, `KL(ℙ₁, ℙ₂) = KL(ℙ₁ ⊗ λ, ℙ₂ ⊗ λ)`. Here `λ` is the Lebesgue measure on the
unit interval, `volume` on `unitInterval`. -/
theorem lemma_1_product {Γ : Type*} [MeasurableSpace Γ] (P₁ P₂ : Measure Γ)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    klDiv P₁ P₂ =
      klDiv (P₁.prod (volume : Measure unitInterval)) (P₂.prod (volume : Measure unitInterval)) := by sorry

end ExploreFirst.FundIneq
