-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_lemma_A_1
-- name    : BanditCovariates.ABSE.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:59.269259+00:00
-- url     : https://prove2.me/theorems/ab54d5be-3e6d-47f2-a2f9-0eb166d5eb2a
-- title:
--   Lemma A.1, p. 28 — maximal deviation bound for bounded martingale differences
-- statement:
--   Let $(Z_t)_{t\ge1}$ be a martingale difference sequence whose terms lie almost surely in an interval $[a,b]$ with $a<b$, and let $\bar Z_t=\frac1t\sum_{s=1}^tZ_s$. Then for every $\delta>0$ and every integer $T\ge1$,
--
--   $$\mathbb P\left\{\exists\, t\in\{1,\dots,T\}:\ \bar Z_t\ge\sqrt{\frac{2(b-a)^2}{t}\log\Big(\frac4\delta\cdot\frac Tt\Big)}\right\}\le\delta.$$
--
--   It controls all sample sizes up to $T$ at once, and is what bounds the probability that the successive elimination run in a cell eliminates a good arm or keeps a bad one.
--
--   **Formalization Note** The first term is centred ($\mathbb E Z_1=0$), which the page's definition of martingale differences leaves out. The page also leaves $a<b$ implicit: for $a=b=0$ the threshold is $0$ and the event has probability one. A general filtration replaces conditioning on $Z_1,\dots,Z_t$. Identical statement to the lemma of the companion successive-elimination mission.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 28, Lemma A.1

import Mathlib
import Definitions.Def_BanditCovariates_SE_MartingaleDifference

namespace BanditCovariates.ABSE

open MeasureTheory ProbabilityTheory

/-- Lemma A.1, p. 28, with the initial centering needed by its first-round case. -/
theorem lemma_A_1 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ)
    (hZ : BanditCovariates.SE.MartingaleDifference P ℱ Z) (a b : ℝ) (hab : a < b)
    (hbound : ∀ n, ∀ᵐ ω ∂P, a ≤ Z n ω ∧ Z n ω ≤ b)
    (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hT : 1 ≤ T) :
    P.real {ω | ∃ t ∈ Finset.Icc 1 T,
      Real.sqrt ((2 * (b - a) ^ 2 / (t : ℝ)) *
        Real.log ((4 * (T : ℝ)) / (δ * (t : ℝ)))) ≤
          (∑ s ∈ Finset.range t, Z s ω) / (t : ℝ)} ≤ δ := by sorry

end BanditCovariates.ABSE
