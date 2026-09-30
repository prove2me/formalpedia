-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_claim_4_8
-- name    : AlgMechDesign.LowerBound.claim_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:50:58.189118+00:00
-- url     : https://prove2.me/theorems/54edad0d-b77f-445e-8569-19d15b0108e8
-- title:
--   Claim 4.8 — perturbing agent 1 toward its bundle keeps the allocation
-- statement:
--   Consider two agents and $k \ge 3$ tasks, and a truthful direct mechanism $(x,p)$. Let $t$ be the type vector with $t^i_j = 1$ for both agents and all tasks, and suppose $|x^1(t)| \le |x^2(t)|$. Let $x = x^1(t)$ and let $\bar x$ be its complement ($=x^2(t)$). For $0<\varepsilon<1$ define $\hat t = t(x \xrightarrow{1} \varepsilon,\ \bar x \xrightarrow{1} 1+\varepsilon)$: agent 1's time becomes $\varepsilon$ on every task of $x$ and $1+\varepsilon$ on every task of $\bar x$, and agent 2's type is unchanged. Then
--
--   $$
--   x(\hat t) = x(t).
--   $$
--
--   This is the step that forces a truthful mechanism to keep a poor allocation on an instance where a much better one exists.
--
--   **Formalization Note** The paper's agents 1 and 2 are `0` and `1` in `Fin 2`. The all-ones vector, the set $x$ and the perturbed vector $\hat t$ are binders fixed by equations. The hypotheses $k\ge3$ and $|x^1(t)|\le|x^2(t)|$ are the paper's standing assumptions for the claim (the latter is its "without loss of generality").
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 179, Notation t(X ->^i alpha), setting paragraph and Claim 4.8

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

/-- Claim 4.8: two agents (the paper's agents 1 and 2 are `0` and `1`), `k ≥ 3` tasks, a
truthful direct mechanism, `t` the all-ones type vector with `|x¹(t)| ≤ |x²(t)|`, `x = x¹(t)`.
For `0 < ε < 1`, let `t̂` lower agent 1's times to `ε` on `x` and raise them to `1 + ε` on the
complement. Then the mechanism allocates at `t̂` exactly as at `t`. -/
theorem claim_4_8 {k : ℕ} (hk : 3 ≤ k) (alloc : (Fin 2 → Fin k → ℝ) → (Fin k → Fin 2))
    (pay : (Fin 2 → Fin k → ℝ) → Fin 2 → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin 2 → Fin k → ℝ) (ht : t = fun _ _ => 1)
    (hcard : (taskSet (alloc t) 0).card ≤ (taskSet (alloc t) 1).card)
    (x : Finset (Fin k)) (hx : x = taskSet (alloc t) 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (that : Fin 2 → Fin k → ℝ)
    (hthat : that = Function.update t 0 (fun j => if j ∈ x then ε else 1 + ε)) :
    alloc that = alloc t := by sorry

end AlgMechDesign.LowerBound
