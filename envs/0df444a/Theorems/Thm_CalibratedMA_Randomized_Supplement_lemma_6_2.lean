-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_6_2
-- name    : CalibratedMA.Randomized.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:07.011036+00:00
-- url     : https://prove2.me/theorems/1a089b45-60ab-4563-9713-8032d16533b5
-- title:
--   Lemma 6.2 — Sample cost of recovering hidden coordinates
-- statement:
--   There is a universal $c_{\rm info}>0$. Choose either alphabet $B=\{0,1\}$ or $B=\{-1,1\}$, an integer $R\ge1$, an offset $\eta>0$, and baselines $t_i\in[0,1]$. Assume every $\theta\in B^R$ gives means $\mu_i^\theta=t_i+\eta\theta_i\in[1/8,7/8]$. Let $D_\theta$ have uniform context marginal on $[R]$ and Bernoulli labels with these means. A single measurable estimator based on $n$ iid examples and an independent seed, with values in $B^R$, satisfies
--   $$\forall\theta\in B^R,\qquad\Pr_\theta\{d_H(\widehat\theta,\theta)\le R/5\}\ge2/3
--   \quad\Longrightarrow\quad n\ge c_{\rm info}R/\eta^2.$$
--   Here $d_H$ counts unequal coordinates; the estimator has no access to $\theta$. This information bound supports both Theorems 6.1 and 7.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: either hidden alphabet and an independent seed estimator → a Boolean choice of alphabet and a single measurable data-and-seed estimator; reason: keeps both alphabets and makes the stated success probabilities ordinary probabilities
--   - encoding: uniform contexts and Bernoulli labels → the explicit finite mixture offsetData; reason: its means are constrained for every hidden vector exactly as in the source
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 32-33, Lemma 6.2 (PDF pp. 34-35)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 6.2, pp.32–33: the same estimator for every hidden vector, either alphabet. -/
theorem lemma_6_2 :
    ∃ c_info : ℝ, 0 < c_info ∧ ∀ (signed : Bool) (R : ℕ), 1 ≤ R →
      ∀ (η : ℝ), 0 < η → ∀ t : Fin R → ℝ,
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ θ : Fin R → ℝ, (∀ i, θ i ∈ Alphabet signed) →
        ∀ i, t i + η * θ i ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)) →
      ∀ (n : ℕ) (seed : TrainingSeed)
        (estimate : ((Fin n → Fin R × ℝ) × seed.Ω) → Fin R → ℝ),
      Measurable estimate → (∀ z i, estimate z i ∈ Alphabet signed) →
      (∀ θ : Fin R → ℝ, (∀ i, θ i ∈ Alphabet signed) →
        ENNReal.ofReal (2 / 3 : ℝ) ≤ trainingLaw n (offsetData t η θ) seed
          {z | (hamming (estimate z) θ : ℝ) ≤ (R : ℝ) / 5}) →
      (n : ℝ) ≥ c_info * R / η ^ 2 := by sorry

end CalibratedMA.Randomized.Supplement
