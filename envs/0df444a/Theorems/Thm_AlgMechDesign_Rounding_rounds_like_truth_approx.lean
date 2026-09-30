-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_rounds_like_truth_approx
-- name    : AlgMechDesign.Rounding.rounds_like_truth_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:17:54.703081+00:00
-- url     : https://prove2.me/theorems/1f9759f7-e64e-42cd-b987-93b354e02a1c
-- title:
--   Proof of Theorem 5.9 — when all agents round like the truth, the outcome is a $(1+\varepsilon)$-approximation
-- statement:
--   Consider the rounding mechanism for bounded scheduling with times in $[a,b]$, $0 < a < b$, a fixed $\varepsilon > 0$, a rounding step $0 < \delta \le \varepsilon a$, and an allocation algorithm $x(\cdot)$ that exactly solves the rounded problem (ties arbitrary). Let $t \in [a,b]^{n\times k}$ be the agents' true types. Suppose every agent $l$ declares $d^l \in [a,b]^k$ with $\hat d^l = \hat t^l$ and uses a feasible execution plan whose rounded actual times equal the rounded true times on its own tasks, for every decision. Let $x = x(d)$ and let $\tilde t$ be the resulting actual times. Then
--   $$g(x,\tilde t) = \max_l \sum_{j \in x^l} \tilde t_j \;\le\; (1+\varepsilon)\, g(y,t)\quad\text{for every allocation } y.$$
--
--   The make-span is measured with the actual execution times, the objective of the problem with verification (Definition 20).
--
--   **Formalization Note** The statement holds for every $\delta \in (0,\varepsilon a]$, which covers the intended choice $\delta = \varepsilon a$. The hypothesis on executions is imposed for every decision, as in the paper's description of the strategies; the upper bound $b$ is not used.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 193, proof (sketch) of Theorem 5.9, third sentence

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

namespace AlgMechDesign.Rounding

/-- Proof of Theorem 5.9, third sentence (p. 193): when every agent follows a strategy of the
class `RoundsLikeTruth` (declaration in `[a, b]ᵏ` with the same rounded value as its true type,
feasible executions whose rounded times equal the rounded true times), the outcome of the rounding
mechanism is a `(1 + ε)`-approximation: its make-span, measured with the actual execution times,
is at most `1 + ε` times the make-span of every allocation under the true types. -/
theorem rounds_like_truth_approx {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (halloc : IsRoundedOptimal a b δ alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsBoundedType a b t)
    (D : Fin n → Fin k → ℝ) (hD : IsBoundedType a b D) (E : Fin n → ExecPlan n k)
    (hE : ∀ l : Fin n, FeasibleExec l (t l) (E l))
    (hR : ∀ l : Fin n, RoundsLikeTruth δ l (t l) (D l) (E l)) :
    ∀ y : Fin k → Fin n, gT (alloc D) (actualTimes alloc D E) ≤ (1 + ε) * makespan t y := by sorry

end AlgMechDesign.Rounding
