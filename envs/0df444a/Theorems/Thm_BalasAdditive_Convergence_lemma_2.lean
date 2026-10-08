-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_lemma_2
-- name    : BalasAdditive.Convergence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:34:30.615159+00:00
-- url     : https://prove2.me/theorems/bf848a81-303c-46e1-8e60-56c9b30b28b0
-- title:
--   Lemma 2 — earlier feasible completions avoid their cancellation snapshot
-- statement:
--   Let $u^k$ and $u^s$ be generated solutions with $k<s$ and $J_k\subset J_s$. Suppose that for every $p$ with $k<p\le s$, the originally formed improving set $N_p$ has been completely cancelled during the processing of $u^s$. If a feasible binary assignment $J_t$ strictly contains $J_k$ and has cost below $z^{*(s)}$, then
--
--   $$(J_t\setminus J_k)\cap C_k^s=\varnothing.\tag{53}$$
--
--   The conclusion restricts better completions of an earlier solution to indices outside its cancellation snapshot.
--
--   **Formalization Note** The hypothesis covers every $p$ in the printed range, not merely ancestors of $J_s$. The paper's $C_p^{s+1}$ (the cancellations made before $u^{s+1}$ is obtained) is read in a state $\tau$ that is either the current state of iteration $s+1$ (cancellations so far; this also covers an iteration that ends with a stop) or the successor state in which $u^{s+1}$ is obtained, whose records are exactly $C_p^{s+1}$. Cancellations only grow and stay inside $N_p$, so the second choice is the printed lemma and the first is an instance of it. $C_k^s$ is the stored snapshot from the moment $u^s$ was obtained, and the ceiling is $z^{*(s)}$. The state is reachable, and $J_t$ need not have been generated.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 532, Lemma 2, Eq. (53), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Lemma 2, p. 532, equation (53). `σ` is a state of iteration `s + 1` (`u^s` is the
latest generated solution). The printed `C_p^{s+1}` is read in `τ`: either `τ = σ`
(the cancellations accumulated so far, which also covers an iteration that ends in a
stop), or `τ` is the successor of `σ` in which `u^{s+1}` is obtained, whose records are
exactly the cancellations made before `u^{s+1}` was obtained. -/
theorem lemma_2 {n m : ℕ} (P : Problem n m) (σ τ : State n)
    (hr : Reachable P σ)
    (hτ : τ = σ ∨ (Step P σ τ ∧ τ.history.length = σ.history.length + 1)) (k : ℕ)
    (hk : k < σ.history.length - 1)
    (hancestor : σ.J k ⊂ σ.latest)
    (hcancel : ∀ p, k < p → p ≤ σ.history.length - 1 → σ.N p = τ.currentC p)
    (J : Finset (Fin n)) (hfeas : P.lp.Feasible J)
    (hstrict : σ.J k ⊂ J)
    (hcost : (↑(P.lp.cost J) : WithTop ℝ) < ceiling P σ) :
    Disjoint (J \ σ.J k) (σ.snapshotC k) := by sorry

end BalasAdditive.Convergence
