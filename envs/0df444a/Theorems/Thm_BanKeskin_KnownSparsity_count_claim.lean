-- Prove2me | Theorems.Thm_BanKeskin_KnownSparsity_count_claim
-- name    : BanKeskin.KnownSparsity.count_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:03.339932+00:00
-- url     : https://prove2.me/theorems/360fd2d7-8d04-41f8-b3e1-3efe106d2bea
-- title:
--   §4.1.1, p. 5555 — each experimental price is charged at least √t/4 times
-- statement:
--   Under the schedule $\mathcal M_1=\{L^2:L\ge1\}$ and $\mathcal M_2=\{L^2+1:L\ge1\}$, let $N_i(t)$ count the periods up to $t$ in which the experimental price $m_i$ is charged. For either $i\in\{1,2\}$ and every integer $t\ge5$,
--
--   $$N_i(t)\ge\frac14\sqrt t.$$
--
--   This is the deterministic frequency guarantee used to lower-bound the variation of experimental prices.
--
--   **Formalization Note** The two prices are indexed by `Fin 2`, with Lean index zero corresponding to $m_1$.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), §4.1.1, p. 5555, after (7)

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

namespace BanKeskin.KnownSparsity

/-- The count assertion after (7), p. 5555. -/
theorem count_claim (i : Fin 2) (t : ℕ) (ht : 5 ≤ t) :
    (1 / 4 : ℝ) * Real.sqrt (t : ℝ) ≤ (experimentCount i t : ℝ) := by sorry

end BanKeskin.KnownSparsity
