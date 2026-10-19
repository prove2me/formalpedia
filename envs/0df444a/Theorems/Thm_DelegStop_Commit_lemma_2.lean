-- Prove2me | Theorems.Thm_DelegStop_Commit_lemma_2
-- name    : DelegStop.Commit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:12.81064+00:00
-- url     : https://prove2.me/theorems/af88dbd5-6d1e-4a8e-800b-3ee01305968f
-- title:
--   Lemma 2, p. 6322 (PDF 7), at T = 2 — with the same effort in every round, flexible stopping weakly beats committed stopping
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2, with evaluation cost $c_I > 0$ and payment $p > 0$, and suppose the provider exerts the same effort $\mu \in \{\mu_l, \mu_h\}$ in every round and after every history. Let $\Pi^C_1(\mu)$ be the committed client's expected profit and $\Pi^F_1(\mu)$ the flexible client's, who stops after a feasible first solution exactly when stopping is at least as good as continuing. Then
--   $$\Pi^C_1(\mu) \le \Pi^F_1(\mu).$$
--
--   This is the benchmark (§3.3.2) against which Proposition 4 is measured: without the provider's strategic effort adjustment, flexibility is never worse.
--
--   **Formalization Note.** Only $T = 2$ is modelled; the page states the lemma for any finite number of rounds. "Benefits" is read as weak dominance, as the page's own discussion says ("the flexible policy (weakly) dominates the committed policy").
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6322 (PDF 7), §3.3.2, Lemma 2 (at T = 2)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem lemma_2 (P : Params) (hP : P.Standing) (cI p : ℝ) (hcI : 0 < cI) (hp : 0 < p)
    (e : Effort) :
    valueC P cI p e e ≤ valueF P cI p e e e := by sorry

end DelegStop.Commit
