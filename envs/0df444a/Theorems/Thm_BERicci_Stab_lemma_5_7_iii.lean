-- Prove2me | Theorems.Thm_BERicci_Stab_lemma_5_7_iii
-- name    : BERicci.Stab.lemma_5_7_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:31.894116+00:00
-- url     : https://prove2.me/theorems/f945c9c7-6b2d-41eb-9585-b01397e43b9b
-- title:
--   Lemma 5.7(iii) — continuous maps of linear growth preserve graph-law convergence
-- statement:
--   Let $f_n\to f_\infty$ in the sense of Definition 5.6, for functions with values in $\mathbb R^k$. If $r:\mathbb R^k\to\mathbb R^h$ is continuous and has linear growth, then
--
--   $$r\circ f_n\longrightarrow r\circ f_\infty$$
--
--   in the same graph-law sense. This allows transformations of heat-flow approximants to be passed through the limit.
--
--   **Formalization Note** Linear growth is $\|r(v)\|\le A+B\|v\|$ for some nonnegative $A,B$. The nonnegative choice is equivalent to the paper's unqualified linear-growth constants.
-- source:
--   arXiv:1209.5786v4, Lemma 5.7(iii), p. 64

import Mathlib
import Definitions.Def_BERicci_Stab_Convergence

namespace BERicci.Stab

open MeasureTheory

/-- Lemma 5.7(iii), p. 64: continuous maps with linear growth preserve graph-law convergence. -/
theorem lemma_5_7_iii {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    {k h : ℕ} (m : ℕ → Measure X) (mlim : Measure X)
    (f : ℕ → X → EuclideanSpace ℝ (Fin k))
    (flim : X → EuclideanSpace ℝ (Fin k))
    (r : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin h))
    (hr : Continuous r)
    (hr_growth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ v, ‖r v‖ ≤ A + B * ‖v‖)
    (hf : FunctionConverges m mlim f flim) :
    FunctionConverges m mlim (fun n => r ∘ f n) (r ∘ flim) := by sorry

end BERicci.Stab
