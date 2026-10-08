-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_lemma2
-- name    : BesbesZeevi.Parametric.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:02:47.431163+00:00
-- url     : https://prove2.me/theorems/01a04378-1f76-473b-b07c-22fd40249ee0
-- title:
--   Lemma 2 — two Poisson deviation bounds
-- statement:
--   Let $0\le\mu\le M$, $\eta>0$, $\beta>0$, and $r_n\ge n^\beta$. For a Poisson count $Z\sim\operatorname{Poisson}(\mu r_n)$, set $\epsilon_n=2\sqrt{\eta M}\sqrt{\log n}/\sqrt{r_n}$. There is a positive constant $C$, depending only on $M,\eta,\beta$, such that for every $n\ge1$,
--
--   $$\mathbb P(Z-\mu r_n>r_n\epsilon_n)\le\frac C{n^\eta},\qquad \mathbb P(Z-\mu r_n<-r_n\epsilon_n)\le\frac C{n^\eta}.$$
--
--   Both tails control errors in the test-price demand estimates. **Formalization Note** The count is represented directly by Mathlib's Poisson measure.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Lemma 2

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Model

namespace BesbesZeevi.Parametric

open MeasureTheory ProbabilityTheory

/-- Lemma 2, p. 27: both Poisson tails, with the paper's explicit epsilon. -/
theorem lemma2 (M η β : ℝ) (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (μ r : ℝ), μ ∈ Set.Icc 0 M →
        (n : ℝ) ^ β ≤ r →
        let eps := 2 * Real.sqrt η * Real.sqrt M *
          Real.sqrt (Real.log (n : ℝ)) / Real.sqrt r
        (poissonMeasure (Real.toNNReal (μ * r)))
          {z : ℕ | (z : ℝ) - μ * r > r * eps} ≤
          ENNReal.ofReal (C / (n : ℝ) ^ η) ∧
        (poissonMeasure (Real.toNNReal (μ * r)))
          {z : ℕ | (z : ℝ) - μ * r < -(r * eps)} ≤
          ENNReal.ofReal (C / (n : ℝ) ^ η) := by sorry

end BesbesZeevi.Parametric
