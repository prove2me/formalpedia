-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_4_1
-- name    : FasterWCTFPTAS.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:37.854222+00:00
-- url     : https://prove2.me/theorems/26b24c84-c6bd-40cb-bf5f-cc37941d6b3e
-- title:
--   Lemma 4.1 — the DP recurrence for DP_i
-- statement:
--   Fix $m\ge2$ machines and a sorted instance with $p_j>0$, $w_j\ge0$. For every $i\in[n]$,
--
--   $$
--   \mathrm{DP}_i=\{(\pi+e_kp_i,\ \theta+w_i(\pi_k+p_i)):(\pi,\theta)\in\mathrm{DP}_{i-1},\ k\in[m-1]\}\cup\{(\pi,\ \theta+w_i(T_{i-1}-\|\pi\|_1+p_i)):(\pi,\theta)\in\mathrm{DP}_{i-1}\},
--   $$
--
--   where $e_k\in\{0,1\}^{m-1}$ is the indicator vector of coordinate $k$. Here $\mathrm{DP}_i$ is the set of pairs (load vector of the first $m-1$ machines, cost) over all schedules of the first $i$ jobs in which each machine processes its jobs in increasing order of index.
--
--   This is the classical load-vector dynamic program; the FPTAS runs it on representative subsets instead of the full sets.
--
--   **Formalization Note** The job `i : Fin n` is the paper's job $i+1$, so the Lean statement reads $\mathrm{DP}_{i+1}=\mathrm{recur}_i(\mathrm{DP}_i)$ with $T_i$ in the role of the paper's $T_{(i+1)-1}$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and i ∈ [n] → jobs Fin n indexed from 0; the job i : Fin n is the paper's job i + 1, so the statement is about DP_{i+1} and DP_i; reason: index shift only; T p i is the paper's T_{(i+1)−1}
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 12 (PDF p. 13), Lemma 4.1

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 4.1, p. 12 (PDF 13): the DP recurrence. For the job `i : Fin n` (the paper's job
`i + 1`), `DP_{i+1} = recur_i(DP_i)`, i.e.
`DP_{i+1} = {(π + e_k p_i, θ + w_i(π_k + p_i)) : (π, θ) ∈ DP_i, k ∈ [m−1]}
          ∪ {(π, θ + w_i(T_i − ‖π‖₁ + p_i)) : (π, θ) ∈ DP_i}`.
Hypotheses: §4's standing assumptions (`m ≥ 2`, `p_j > 0`, jobs sorted by Smith's ratio). -/
theorem lemma_4_1 {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : Fin n) :
    DP m p w (i.val + 1) = recur m p w i (DP m p w i.val) := by sorry

end FasterWCTFPTAS.Main
