-- Prove2me | Theorems.Thm_DermanSeqDecisions_Ratio_avg_nonpos_of_ratio_le
-- name    : DermanSeqDecisions.Ratio.avg_nonpos_of_ratio_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:45:56.828336+00:00
-- url     : https://prove2.me/theorems/9864162a-e031-4100-aa39-1e5960281eb8
-- title:
--   A ratio criterion at most $m$ gives a nonpositive average cost for $w' - m w''$
-- statement:
--   Consider a controlled Markov chain with finitely many states and decisions, all decisions available in every state. Let $w'_{ik} > 0$ and $w''_{ik} > 0$ be two sets of costs, and let $R$ be any procedure (history-dependent and randomized), started at $X_0 = i$, with expected costs $W'_t$ and $W''_t$ at time $t$. If its ratio criterion satisfies
--   $$\psi_R(i) = \limsup_{T\to\infty} \frac{\sum_{t=0}^T W'_t}{\sum_{t=0}^T W''_t} \le m ,$$
--   then the average expected cost of $R$ for the signed costs $w_{ik} = w'_{ik} - m\, w''_{ik}$ satisfies
--   $$Q_R(i) = \limsup_{T\to\infty} \frac1T \sum_{t=0}^T W_t \le 0 .$$
--
--   This is the step "Using rule $R(v)$ we have $Q_{R(v)}(i) \le 0$" of the proof of Theorem 3: it translates the ratio criterion into the ordinary average-cost criterion of Problem 1.
--
--   **Formalization Note** The page uses $\psi_{R(v)}(i) = m_v$; the hypothesis $\psi_R(i) \le m$ includes that case. The costs are explicit real arguments; the nonnegative cost field of Sennott's model plays no role.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 23, §4, proof of Theorem 3

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **"Using rule R(v) we have Q_{R(v)}(i) ≦ 0."** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23).

Let `w′ > 0`, `w″ > 0` be two cost sets. If a procedure `θ` has ratio criterion
`ψ_θ(i) ≤ m`, then the long-run average expected cost of `θ` for the signed cost
`w_ik = w′_ik − m w″_ik` satisfies `Q_θ(i) ≤ 0`.

**Formalization Note.** The page has `ψ_{R(v)}(i) = m_v`; the hypothesis `ψ_θ(i) ≤ m` contains
that case. `θ` is an arbitrary history-dependent randomized procedure. `M.C` plays no role. -/
theorem avg_nonpos_of_ratio_le {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (i : S) (m : ℝ) (hψ : ratioCost θ i w' w'' ≤ m) :
    avgCostR θ i (fun s a => w' s a - m * w'' s a) ≤ 0 := by sorry

end DermanSeqDecisions.Ratio
