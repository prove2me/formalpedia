-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_def_1_equiv
-- name    : AddLogReg.Multiclass.def_1_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:33.479002+00:00
-- url     : https://prove2.me/theorems/aba2c530-a19f-448c-a206-8cc86ab67ec3
-- title:
--   Definition 1, p. 354 — the symmetric multiple logistic transformation (39) is equivalent to (40) with Σ F_k = 0
-- statement:
--   Let $J\ge1$ and let $p=(p_1,\dots,p_J)$ be a probability vector with all entries positive: $p_j>0$ and $\sum_j p_j = 1$. For any real vector $F=(F_1,\dots,F_J)$ the following are equivalent:
--
--   1. $F$ is the symmetric multiple logistic transformation (39) of $p$:
--   $$F_j = \log p_j - \frac1J\sum_{k=1}^J\log p_k\qquad(j=1,\dots,J);$$
--   2. $F$ satisfies (40):
--   $$p_j = \frac{e^{F_j}}{\sum_{k=1}^J e^{F_k}}\quad(j=1,\dots,J),\qquad \sum_{k=1}^J F_k = 0 .$$
--
--   This is the equivalence of the two forms of Definition 1. It says that (39) is the unique centred inverse of the softmax map (40), and is what lets the multiclass LogitBoost algorithm work on the centred scores $F_j$ and recover probabilities through (40).
--
--   **Formalization Note** The positivity of every $p_j$ is what "$p_j(x) = P(y_j = 1\mid x)$" with $\log p_j$ defined requires: Lean's `Real.log 0 = 0` would otherwise give (39) a junk value. The vector form is the statement at a fixed $x$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, Definition 1, (39)–(40) and the sentence after (40)

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem def_1_equiv {J : ℕ} [NeZero J] (p : Fin J → ℝ) (hp_pos : ∀ j, 0 < p j)
    (hp_sum : ∑ j, p j = 1) (F : Fin J → ℝ) :
    F = symMultiLogit p ↔ ((∀ j, p j = softmax F j) ∧ ∑ k, F k = 0) := by sorry

end AddLogReg.Multiclass
