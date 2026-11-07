-- Prove2me | Theorems.Thm_AdaptiveSparsify_theorem_3
-- name    : AdaptiveSparsify.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:45:56.160431+00:00
-- url     : https://prove2.me/theorems/3bdf4b3f-34f5-4808-b53f-742a2fb23a64
-- title:
--   Theorem 3 — leverage score overestimates under adaptive row updates in time $\tilde O(nd+Qd^6)$
-- statement:
--   There is one program that, given a matrix $A\in\mathbb R^{n\times d}$ undergoing $Q$ batches of adaptive row insertions and deletions of total size at most $C_0n$, and $\kappa$ with $\kappa^{-1}I\preceq A^\top A\preceq\kappa I$ at all times, maintains overestimates $\tilde\tau_i$ of the leverage scores $\tau_i=a_i^\top(A^\top A)^{-1}a_i$ such that, with probability at least $1-(n+2)^{-c}$,
--
--   1. $\tilde\tau_i\ge\tau_i$ for all $i$, at every point at which the estimates are published;
--   2. $\sum_{i=1}^n\tilde\tau_i\le Cd(\log(n+d+\kappa+2))^k$;
--   3. the total work is at most $C(nd+(Q+1)d^6)(\log(n+d+\kappa+2))^k$.
--
--   The adversary sees the published estimates and chooses the next batch from them; it does not see the randomness. This is the paper's main technical contribution: the rows themselves change and inserted rows have no history, and the leading term $nd$ is only the cost of reading them. It is what makes the interior point method of Theorem 1 run in nearly linear time.
--
--   Differences from the source:
--   - reading: row insertions/deletions → n row slots and updates (i, v): v = 0 deletes, writing to an empty slot inserts; reason: the update form of Lemma 2.2, p.11, Modify(i, v), "where v = 0 is equivalent to deleting it"
--   - reading: runtime Õ(nd + Qd⁶) for Q batches → C (nd + (Q + 1) d⁶)(log(n + d + κ + 2))^k, with Q the number of batches delivered and C, k chosen before the instance; reason: the initial matrix is read as the first batch (its n rows are insertions, counted in the total size O(n), and p.33 charges its initialization like every rebuild, Õ(nd + d^{3+ω})), so the number of batches is Q + 1 with Q the batches delivered afterwards; for Q ≥ 1 also Q + 1 ≤ 2Q
--   - encoding: n, d unrestricted → n ≥ 1, d ≥ 1; reason: at d = 0 the time bound is 0 and no program can run; at n = 0 and d ≥ 1 the promise κ⁻¹I ⪯ A⊤A fails
--   - reading: "at all times" the Gram promise holds, total size O(n) → a batch breaking the promise, or the total C₀ n, ends the game at that moment, with everything published before it still required to be correct; the initial matrix meets the promise; reason: the promise binds along the run, so an adversary breaching it on some tapes does not make the event vacuous on the others; on tapes without a breach this is the printed promise
--   - reading: "adaptive" → a deterministic strategy, measurable in the history of published τ̃, which never sees the tape; reason: pp.11, 37: the outputs reveal only what the checker determines; the bad event is bounded in outer measure, which has no content against a non-measurable function
--   - reading: no probability printed → failure at most (n + 2)^{−c} for every c > 0, one event for all clauses, with the program and constants chosen after c; reason: the algorithm is randomized and its proof is "with high probability" (Lemma 5.5); base n + 2 avoids a vacuous bound at n = 1
--   - reading: "an algorithm" → one finite admissible program of the barrier-oracle RAM (no barrier reachable here); estimates published at yield, input delivered to memory; reason: readings R3 and R4; reading τ̃ is free for the adversary and work counts machine steps
--   - encoding: Q batches → a cap Q on the batches delivered, unknown to the program; reason: the program does not receive Q, which only strengthens the statement
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 3, p.7

import Mathlib
import Definitions.Def_AdaptiveSparsify_DynamicGame

open Matrix

namespace AdaptiveSparsify

/-- **Theorem 3**, p.7.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Theorem 3, p.7.

"There is an algorithm that given a dynamic matrix A ∈ R^{n×d} undergoing Q batches of adaptive row
insertions/deletions with total size at most O(n), and a parameter κ such that at all times the Gram
matrix A⊤A satisfies (1/κ)I ⪯ A⊤A ⪯ κI, maintains overestimates τ̃_i of the leverage scores
τ_i := a_i⊤(A⊤A)⁻¹a_i of the rows a_i⊤ of A satisfying: τ̃_i ≥ τ_i = a_i⊤(A⊤A)⁻¹a_i, and
∑_{i=1}^n τ̃_i ≤ Õ(d). The total runtime is at most Õ(nd + Qd⁶). Here (and throughout this paper) Õ(·)
hides polylog factors in n, d, and κ."

**Formalization Note.** The game is `AdaptiveSparsify.DynamicGame`: one program for all `n, d, κ, Q`
and every measurable adaptive adversary. The constant in "total size at most O(n)" is `C₀`, chosen
first. The bound is `C (nd + (Q + 1) d⁶)(log(n + d + κ + 2))^k`, with `Q` the number of delivered
batches. The initial matrix must meet the promise; a later breach ends the game, with everything
published so far still required to be correct. -/
theorem theorem_3 : ∀ C₀ : ℝ, 0 < C₀ → ∀ c : ℝ, 0 < c →
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) (Q : ℕ) (σ : Strategy n d),
        1 ≤ n → 1 ≤ d → 0 < κ → σ.Measurable → GramPromise κ A →
        tape {ω | ¬ GameSuccess P σ A κ C₀ Q C k ω} ≤
          ENNReal.ofReal (((n : ℝ) + 2) ^ (-c)) := by sorry

end AdaptiveSparsify
