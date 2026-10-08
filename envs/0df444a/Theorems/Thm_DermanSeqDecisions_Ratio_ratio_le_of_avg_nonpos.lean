-- Prove2me | Theorems.Thm_DermanSeqDecisions_Ratio_ratio_le_of_avg_nonpos
-- name    : DermanSeqDecisions.Ratio.ratio_le_of_avg_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:46:06.469205+00:00
-- url     : https://prove2.me/theorems/7658546f-63d7-4a3a-b7f0-2ea8e96f4c39
-- title:
--   For a deterministic stationary procedure, a nonpositive average cost for $w' - m w''$ gives a ratio criterion at most $m$
-- statement:
--   Consider a controlled Markov chain with finitely many states and decisions, all decisions available in every state, satisfying Assumption A (for every stationary randomized procedure all states belong to the same class). Let $w'_{ik} > 0$ and $w''_{ik} > 0$ be two sets of costs, let $R^* \in C''$ be a deterministic stationary procedure, and let $X_0 = i$. If the average expected cost of $R^*$ for the signed costs $w_{ik} = w'_{ik} - m\, w''_{ik}$ satisfies
--   $$Q_{R^*}(i) = \limsup_{T\to\infty} \frac1T \sum_{t=0}^T W_t \le 0 ,$$
--   then
--   $$\psi_{R^*}(i) = \limsup_{T\to\infty} \frac{\sum_{t=0}^T W'_t}{\sum_{t=0}^T W''_t} \le m .$$
--
--   This is the step "$Q_{R^*(v)}(i) \le 0$, which implies $\psi_{R^*(v)}(i) \le m_v$" of the proof of Theorem 3. It is the converse of the previous step, and it is stated only for stationary procedures, as on the page, and under Assumption A, which the proof of Theorem 3 assumes and which the page's justification (the display for $\psi_R$, $R \in C'$) needs.
--
--   **Formalization Note** The costs are explicit real arguments; the nonnegative cost field of Sennott's model plays no role.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 23, §4, proof of Theorem 3

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **"…which implies ψ_{R*(v)}(i) ≦ m_v."** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23).

Assume Assumption A, let `w′ > 0`, `w″ > 0` be two cost sets and `f ∈ C″` a deterministic
stationary procedure. If the long-run average expected cost of `f` for the signed cost `w_ik = w′_ik − m w″_ik`
satisfies `Q_f(i) ≤ 0`, then `ψ_f(i) ≤ m`.

**Formalization Note.** The statement is for stationary `f` only, as on the page (`R*(v) ∈ C″`);
for history-dependent procedures the implication can fail. Assumption A is a hypothesis because
the step is made inside the proof of Theorem 3, which assumes it, and the page justifies it through
the display for `ψ_R`, `R ∈ C′`, which needs it. `M.C` plays no role. -/
theorem ratio_le_of_avg_nonpos {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (f : StationaryPolicy M) (i : S) (m : ℝ)
    (hQ : avgCostR f.toPolicy i (fun s a => w' s a - m * w'' s a) ≤ 0) :
    ratioCost f.toPolicy i w' w'' ≤ m := by sorry

end DermanSeqDecisions.Ratio
