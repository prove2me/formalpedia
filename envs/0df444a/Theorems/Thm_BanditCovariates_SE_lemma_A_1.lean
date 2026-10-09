-- Prove2me | Theorems.Thm_BanditCovariates_SE_lemma_A_1
-- name    : BanditCovariates.SE.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:32.14314+00:00
-- url     : https://prove2.me/theorems/c2162898-b6ab-4491-816b-c0a55c818bea
-- title:
--   Lemma A.1, p. 28 — peeling bound for bounded martingale differences
-- statement:
--   Let $(Z_t)$ be a martingale difference sequence whose terms lie in a nondegenerate interval $[a,b]$, with $a<b$, almost surely. For every $\delta>0$ and integer $T\ge1$, with $\bar Z_t=t^{-1}\sum_{s=1}^{t}Z_s$,
--
--   $$P\!\left\{\exists t\in\{1,\ldots,T\}:\bar Z_t\ge\sqrt{\frac{2(b-a)^2}{t}\log\frac{4T}{\delta t}}\right\}\le\delta.$$
--
--   The lemma controls all sample sizes up to a horizon at once and is used to bound elimination of the best arm.
--
--   **Formalization Note** The first difference has mean zero, which the paper's stated definition of martingale differences leaves implicit. The page also leaves $a<b$ implicit: if $a=b=0$, the threshold is zero and the event has probability one even for $\delta<1$. The result also allows a general adapted filtration in place of conditioning on the sequence's own past.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 28, Lemma A.1

import Mathlib
import Definitions.Def_BanditCovariates_SE_MartingaleDifference

namespace BanditCovariates.SE

open MeasureTheory ProbabilityTheory

/-- Lemma A.1, p. 28, with the initial centering needed by its first-round case. -/
theorem lemma_A_1 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ)
    (hZ : MartingaleDifference P ℱ Z) (a b : ℝ) (hab : a < b)
    (hbound : ∀ n, ∀ᵐ ω ∂P, a ≤ Z n ω ∧ Z n ω ≤ b)
    (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hT : 1 ≤ T) :
    P.real {ω | ∃ t ∈ Finset.Icc 1 T,
      Real.sqrt ((2 * (b - a) ^ 2 / (t : ℝ)) *
        Real.log ((4 * (T : ℝ)) / (δ * (t : ℝ)))) ≤
          (∑ s ∈ Finset.range t, Z s ω) / (t : ℝ)} ≤ δ := by sorry

end BanditCovariates.SE
