-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_no_mechanism_below_two
-- name    : AlgMechDesign.LowerBound.no_mechanism_below_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:00:47.367993+00:00
-- url     : https://prove2.me/theorems/f9572473-3d06-48b6-9e44-a1da153fb1c0
-- title:
--   Theorem 4.6 — no mechanism implements a $c$-approximation for task scheduling for any $c<2$
-- statement:
--   Consider task scheduling on unrelated machines with $n \ge 2$ agents and $k\ge 3$ tasks, where agent $i$ needs time $t^i_j>0$ for task $j$ and the objective is the make-span $g(x,t) = \max_i \sum_{j\in x^i} t^i_j$. Let $c<2$. Then there is no mechanism $m=(o,p)$ — with arbitrary strategy sets $A^1,\dots,A^n$, output function $o$ and payments $p$ — that implements a $c$-approximation with dominant strategies. That is, for every such mechanism, either some agent of some positive type has no dominant strategy, or there are a positive type vector $t$, a tuple $a$ of dominant strategies for $t$ and an allocation $y$ with
--
--   $$
--   g\big(o(a),t\big) > c \cdot g(y,t).
--   $$
--
--   Together with the MinWork mechanism (an $n$-approximation), this shows that for two agents the best approximation ratio achievable by a mechanism is exactly $2$, in contrast with the approximation ratios available to algorithms that ignore incentives.
--
--   **Formalization Note** The thresholds $n\ge2$ and $k\ge3$ come from the proof ("We prove the theorem for the case of two agents. For $n>2$ we can reduce to this case…"; "Let $k\ge3$"); for $n = 1$ the claim is false, since the single agent performing everything is optimal. The statement holds for each fixed $n$ and $k$ and every $c<2$. Strategy sets are arbitrary types in a fixed universe, and implementation requires the existence of dominant strategies for every positive type. Running time is not modelled.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Theorem 4.6 (proof pp. 178-179)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Mechanism

namespace AlgMechDesign.LowerBound

universe u

/-- Theorem 4.6: with at least two agents and at least three tasks, no mechanism — with
arbitrary strategy sets `A i`, output function `o` and payments `p` — implements a
`c`-approximation for the task scheduling problem with dominant strategies, for any `c < 2`. -/
theorem no_mechanism_below_two {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k) {c : ℝ}
    (hc : c < 2) {A : Fin n → Type u} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) :
    ¬ Implements o p c := by sorry

end AlgMechDesign.LowerBound
