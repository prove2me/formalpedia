-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_lemma_3
-- name    : CorreaThreshold.Nonadaptive.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:43.700565+00:00
-- url     : https://prove2.me/theorems/3a7cc051-3b83-4a3c-b199-8cd2e7a38fa7
-- title:
--   Lemma 3, p. 1458 — h_n is nonnegative on its interval
-- statement:
--   For every integer $n\ge1$, let $\bar x=1/(n-1+e/2)$. The function $h_n$ from Lemma 2 obeys
--
--   $$h_n(x)\ge0\qquad\text{for all }x\in[0,\bar x].$$
--
--   Together with Lemma 2, this yields the analytic inequality used by the Bernoulli selection lemma.
--
--   **Formalization Note** The denominator defining $\bar x$ is positive for every $n\ge1$; the index in Lean is the paper's index.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1458, Lemma 3, proof pp. 1469–1470; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- Lemma 3: nonnegativity of `h_n` on the printed interval. -/
theorem lemma_3 :
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Icc (0 : ℝ)
      (1 / ((n : ℝ) - 1 + Real.exp 1 / 2)), 0 ≤ h n x := by sorry

end CorreaThreshold.Nonadaptive
