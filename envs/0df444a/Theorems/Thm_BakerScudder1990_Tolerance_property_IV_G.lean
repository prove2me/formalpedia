-- Prove2me | Theorems.Thm_BakerScudder1990_Tolerance_property_IV_G
-- name    : BakerScudder1990.Tolerance.property_IV_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:11:03.172711+00:00
-- url     : https://prove2.me/theorems/1c516958-d350-4124-9aa4-be5f010432cd
-- title:
--   Property IV(G) — the job $b$ with $b$ jobs untardy completes at $d + v_b$ or $d - u_b$ (corrected labels)
-- statement:
--   Consider an instance of the single-machine common-due-date model with tolerances and $n \ge 1$ jobs in a fixed sequence, processed without inserted idle time, with completion times $C_1,\dots,C_n$, tolerance windows $[d - u_j, d + v_j]$ and unit penalties $\alpha_j, \beta_j > 0$. Then a least optimal due date exists. Let $d$ be the least optimal due date and let $b$ be the number of jobs that incur no tardiness penalty, i.e. with $(C_j - d - v_j)^+ = 0$. Then $b \ge 1$ and exactly one of the following holds:
--
--   $$
--   \begin{aligned}
--   C_b &= d + v_b && \text{and}\quad \sum_{i<b}\alpha_i < \sum_{i\ge b}\beta_i,\quad \sum_{i<b}\alpha_i \ge \sum_{i>b}\beta_i, \\
--   C_b &= d - u_b && \text{and}\quad \sum_{i<b}\alpha_i < \sum_{i> b}\beta_i,\quad \sum_{i\le b}\alpha_i \ge \sum_{i>b}\beta_i.
--   \end{aligned}
--   $$
--
--   In particular, whichever pair of inequalities holds determines at which end of its tolerance window job $b$ completes. This is Property IV(G) of Baker and Scudder, the tolerance generalization of the classical condition that the $b$-th job completes exactly at the common due date; it identifies the candidate V-shaped sequences for optimality.
--
--   **Formalization Note** The printed statement (p. 30, repeated p. 35) pairs the first pair of inequalities with $C_b = d - u_b$ and the second with $C_b = d + v_b$. The paper's own proof (p. 35) derives the first pair as the condition for $d = C_j - v_j$, i.e. $C_j = d + v_j$, and the second for $d = C_j + u_j$, i.e. $C_j = d - u_j$; the statement here follows the proof. A single job with $u_1, v_1 > 0$ shows the printed labels are wrong: $f = 0$ exactly on $[C_1 - v_1, C_1 + u_1]$, so the least optimal due date is $d = C_1 - v_1$, $b = 1$, the first pair holds ($0 < \beta_1$, $0 \ge 0$), and $C_1 = d + v_1 \ne d - u_1$. Positions are 0-based: the paper's job $b$ is position $k = b - 1$, and the count of untardy jobs equals $k+1$. "In an optimal schedule" is read for a fixed sequence and its least optimal due date, which implies the paper's reading. Existence of the least optimal due date is part of the conclusion, so the statement is not vacuous.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 30, Property IV(G); restated and proved pp. 34–35 (Appendix). Case labels as derived in the proof (p. 35); the printed statement swaps them

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Property IV(G) (Baker and Scudder 1990, p. 30), with the case labels as derived in its proof
(p. 35); the printed statement swaps them. For a fixed sequence of `n > 0` jobs processed without
inserted idle time, a least optimal common due date exists; at every least optimal due date `d`,
let `b = k + 1` be the number of jobs with zero tardiness `(C_j - d - v_j)^+ = 0`. Then either
`C_k = d + v_k` with `∑_{i<k} α_i < ∑_{i≥k} β_i` and `∑_{i<k} α_i ≥ ∑_{i>k} β_i`, or
`C_k = d - u_k` with `∑_{i<k} α_i < ∑_{i>k} β_i` and `∑_{i≤k} α_i ≥ ∑_{i>k} β_i`.
Positions are 0-based: the paper's job `b` is position `k` with `b = k + 1`. -/
theorem property_IV_G {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n,
          (Finset.univ.filter (fun j : Fin n => I.tardiness d j = 0)).card = k.val + 1 ∧
          ((I.C k = d + I.v k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i)) ∨
           (I.C k = d - I.u k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i))) := by sorry

end BakerScudder1990.Tolerance
