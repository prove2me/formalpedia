-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_3c
-- name    : DelegStop.Commit.proposition_3c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:13.326451+00:00
-- url     : https://prove2.me/theorems/0b4df3ef-05fc-4a57-af98-909c4e21a5fa
-- title:
--   Proposition 3 (c), p. 6323 (PDF 8) — p̄^C ≤ p̄^F, and p̄^F − p̄^C is nondecreasing in k and nonincreasing in c_I
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2, with evaluation cost $c_I > 0$, and let $(\underline p, \bar p^C)$ and $(\underline p', \bar p^F)$ be effort thresholds as in Proposition 3 (a) and (b).
--
--   **Proposition 3 (c).**
--   1. $\bar p^C \le \bar p^F$.
--   2. $\bar p^F - \bar p^C$ is nondecreasing in $k$: if the thresholds at capability $k$ are $\bar p^C, \bar p^F$ and at capability $k' \ge k$ (all other parameters equal) are $\bar q^C, \bar q^F$, then
--   $$\bar p^F - \bar p^C \le \bar q^F - \bar q^C .$$
--   3. $\bar p^F - \bar p^C$ is nonincreasing in $c_I$: if $\bar p^F_2$ is a flexible threshold at evaluation cost $c_I' \ge c_I$, then $\bar p^F_2 - \bar p^C \le \bar p^F - \bar p^C$.
--
--   The gap $\bar p^F - \bar p^C$ is the range of payments over which the two policies induce different first-round efforts; it is where the committed policy can outperform the flexible one (Proposition 4).
--
--   **Formalization Note.** Only $T = 2$ is modelled. The claims are stated for every choice of thresholds satisfying Proposition 3 (a) and (b); such thresholds are unique, so this is the page's statement about "the" thresholds without assuming existence. The committed threshold $\bar p^C$ does not depend on $c_I$, so one $\bar p^C$ serves in item 3.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6323 (PDF 8), Proposition 3 (c)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_3c (P : Params) (hP : P.Standing) (cI : ℝ) (hcI : 0 < cI) :
    (∀ pLow pBarC pLow₁ pBarF : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
        pBarC ≤ pBarF) ∧
    (∀ k₂ : ℝ, P.k ≤ k₂ → ∀ pLow pBarC pLow₁ pBarF qLow qBarC qLow₁ qBarF : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
      CommittedEffortThresholds { P with k := k₂ } qLow qBarC →
      FlexibleEffortThresholds { P with k := k₂ } cI qLow₁ qBarF →
        pBarF - pBarC ≤ qBarF - qBarC) ∧
    (∀ cI₂ : ℝ, cI ≤ cI₂ → ∀ pLow pBarC pLow₁ pBarF pLow₂ pBarF₂ : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
      FlexibleEffortThresholds P cI₂ pLow₂ pBarF₂ →
        pBarF₂ - pBarC ≤ pBarF - pBarC) := by sorry

end DelegStop.Commit
