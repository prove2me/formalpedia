-- Prove2me | Theorems.Thm_BBBV_RandomOracle_fails_one_of_close
-- name    : BBBV.RandomOracle.fails_one_of_close
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:18.361+00:00
-- url     : https://prove2.me/theorems/fa1c4ae7-208e-47d2-b1fb-6bc415805735
-- title:
--   Proof of Theorem 3.5, p. 9 — if the final states for A ∈ 𝒜 and A_y are within 1/13, M fails on ℒ_A or on ℒ_{A_y}
-- statement:
--   Let $M$ be a $T$-query algorithm whose queries are strings of $\{0,1\}^n$ and whose answers are in $\{0,1\}^n$. Let $A : \{0,1\}^n \to \{0,1\}^n$ be an oracle under which $1^n$ has no preimage, let $y \in \{0,1\}^n$, and let $A_y$ be the oracle with $A_y(y) = 1^n$ and $A_y(z) = A(z)$ for $z \ne y$. If the final states $\varphi_T$ of $M$ with oracle $A$ and $\varphi_T^{(y)}$ with oracle $A_y$ satisfy
--   $$\|\varphi_T - \varphi_T^{(y)}\| \le \frac1{13},$$
--   then $M$ does not both decide "$1^n$ has a preimage under $A$" with oracle $A$ and decide "$1^n$ has a preimage under $A_y$" with oracle $A_y$.
--
--   In the paper's words, $M$ fails to accept either $\mathcal{L}_A$ or $\mathcal{L}_{A_y}$ on input $1^n$: the acceptance probabilities differ by at most $4/13 < 1/3$, while bounded-error decision requires acceptance probability at most $1/3$ under $A$ (where $1^n \notin \mathcal{L}_A$) and at least $2/3$ under $A_y$ (where $1^n \in \mathcal{L}_{A_y}$).
--
--   **Formalization Note** "Deciding" means bounded error with thresholds $2/3$ and $1/3$ on both sides (§2, p. 5). The input $1^n$ is fixed and absorbed into the algorithm's initial state.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 9, proof of Theorem 3.5, fifth paragraph

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

theorem fails_one_of_close {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (A : Str n → Str n) (hA : NoInverse A) (y : Str n)
    (h : ‖final M (fun _ => A) - final M (fun _ => Function.update A y (ones n))‖ ≤ 1 / 13) :
    ¬ (Decides M (fun _ => A) (∃ x, A x = ones n) ∧
      Decides M (fun _ => Function.update A y (ones n))
        (∃ x, Function.update A y (ones n) x = ones n)) := by sorry

end BBBV.RandomOracle
