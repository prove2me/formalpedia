-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_ratio_step
-- name    : AlgMechDesign.Additive.ratio_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:25:54.858374+00:00
-- url     : https://prove2.me/theorems/51f93eed-9ba3-4269-ba36-46eaa7761154
-- title:
--   Proof of Theorem 4.10, ratio step — make-span at least $(1-\epsilon)n$ against an allocation of make-span at most $1+k\epsilon$
-- statement:
--   Let $t$ be the type vector with all entries equal to $1$, $i$ an agent, $x$ a set of exactly $n$ tasks and $0<\epsilon<1$, and let $\hat t = t(x \xrightarrow{i} 1-\epsilon,\ \bar x \xrightarrow{i} \epsilon)$ (agent $i$ needs time $1-\epsilon$ for each task of $x$ and $\epsilon$ for every other task; the other agents need time $1$ for every task). Then:
--
--   1. every allocation $z$ that gives agent $i$ all tasks of $x$ has make-span $g(z,\hat t) \ge (1-\epsilon)\,n$;
--   2. some allocation $y$ has make-span $g(y,\hat t) \le 1 + k\epsilon$.
--
--   Together with Claim 4.11 this yields the ratio $(1-\epsilon)n/(1+k\epsilon)$, which tends to $n$ as $\epsilon\to 0$.
--
--   **Formalization Note** The paper writes $g(x(\hat t),\hat t) \ge |x^1| \ge n$; since agent $1$'s tasks in $x$ each take $1-\epsilon$ under $\hat t$, the bound that follows is $(1-\epsilon)|x^1| \ge (1-\epsilon)n$, stated here. The set $x$ has exactly $n$ tasks, the paper's "we can assume w.l.o.g. that $|x^1| = n$"; the second part is the paper's "an optimal allocation would split these tasks among the $n$ agents", with the explicit bound $1+k\epsilon$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, proof of Theorem 4.10, paragraph after the proof of Claim 4.11 (corrected bound)

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model

namespace AlgMechDesign.Additive

/-- The ratio step of the proof of Theorem 4.10, p. 180, with the printed bound corrected: let
`t` be the all-ones type vector, `i` an agent, `x` a set of exactly `n` tasks, `0 < ε < 1` and
`t̂ = t(x →ⁱ 1 - ε, x̄ →ⁱ ε)`. Every allocation giving agent `i` all tasks of `x` has make-span
at least `(1 - ε) n` under `t̂`, while some allocation has make-span at most `1 + k ε`. -/
theorem ratio_step {n k : ℕ} [NeZero n] (i : Fin n) (x : Finset (Fin k)) (hx : x.card = n)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    (∀ z : Fin k → Fin n, x ⊆ taskSet z i →
        (1 - ε) * n ≤ makespan (Function.update (fun _ _ => (1 : ℝ)) i
          (fun j => if j ∈ x then 1 - ε else ε)) z) ∧
      ∃ y : Fin k → Fin n,
        makespan (Function.update (fun _ _ => (1 : ℝ)) i
          (fun j => if j ∈ x then 1 - ε else ε)) y ≤ 1 + k * ε := by sorry

end AlgMechDesign.Additive
