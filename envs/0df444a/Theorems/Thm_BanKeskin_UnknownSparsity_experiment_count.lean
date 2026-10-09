-- Prove2me | Theorems.Thm_BanKeskin_UnknownSparsity_experiment_count
-- name    : BanKeskin.UnknownSparsity.experiment_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:16.908499+00:00
-- url     : https://prove2.me/theorems/4cf63b3d-8ea5-48cd-992e-668859635be8
-- title:
--   §4.1.1, p. 5555 — for t ≥ 5, each experimental price is charged at least ¼√t times in periods 1, …, t
-- statement:
--   Let $M_1 = \{L^2 : L = 1,2,\dots\}$ and $M_2 = \{L^2+1 : L = 1,2,\dots\}$ be the experimentation periods of the schedule (7) of Ban and Keskin (2021), in which the experimental prices $m_1$ and $m_2$ are charged. Then for every $t \ge 5$,
--
--   $$|M_1\cap\{1,\dots,t\}| \ \ge\ \tfrac14\sqrt t \qquad\text{and}\qquad |M_2\cap\{1,\dots,t\}| \ \ge\ \tfrac14\sqrt t .$$
--
--   This guarantees that the information about the price sensitivity grows at rate $\sqrt t$, which underlies the estimation-error bound of Lemma 3 and hence Theorem 3. ILQX uses the same schedule as ILSX (§4.1.1).
--
--   **Formalization Note.** Periods are 1-based. "Each experimental price is charged" counts the experimentation periods of that price, $|M_i\cap\{1,\dots,t\}|$.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5555, §4.1.1, after (7)

import Mathlib
import Definitions.Def_BanKeskin_UnknownSparsity_Model

namespace BanKeskin.UnknownSparsity

open Classical in
theorem experiment_count (t : ℕ) (ht : 5 ≤ t) :
    (1 / 4 : ℝ) * Real.sqrt t ≤ (((Finset.Icc 1 t).filter fun k => BanKeskin.KnownSparsity.inM1 k).card : ℝ) ∧
      (1 / 4 : ℝ) * Real.sqrt t ≤ (((Finset.Icc 1 t).filter fun k => BanKeskin.KnownSparsity.inM2 k).card : ℝ) := by sorry

end BanKeskin.UnknownSparsity
