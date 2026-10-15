-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_theorem_1_i
-- name    : FairGuarantees.DivideChoose.theorem_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:32.76296+00:00
-- url     : https://prove2.me/theorems/d2b0c5ed-44f7-4419-8afe-7fc471683102
-- title:
--   Theorem 1 i), p. 15 — in Divide & Choose_n the equipartition / accept-above-minMax strategy guarantees minMax(u; n)
-- statement:
--   Fix a manna $\Omega\subseteq\mathbb R^d$ ($d\ge1$), $n\ge1$ agents and an agent $i$ with utility $u\in\mathcal D(\Omega)$. Let $\mu=\mathrm{minMax}(u;n)$ be the minMax level of the initial problem. Agent $i$'s strategy in the D&C$_n$ rule is: when called to divide the remaining share $S$ among the $m$ remaining agents, propose an equipartition $\Pi^e\in\mathcal{EP}_m(S;u)$; when reporting shares, like exactly the shares worth at least $\mu$. Whatever the other agents do (their partitions, their reports, and the choice among proper matchings):
--
--   1. whenever $i$ is called to divide, an equipartition of the remaining manna among the remaining agents exists;
--   2. whenever $i$ must report, some offered share is worth at least $\mu$, so the strategy is a legal report;
--   3. in every complete play in which $i$ follows the strategy, the share $S_i$ that $i$ receives satisfies
--   $$u(S_i)\ge\mathrm{minMax}(u;n).$$
--
--   So the strategy is always available and protects agent $i$ at the minMax level, which makes $\mathrm{minMax}(\cdot;n)$ a Fair Guarantee implemented by the rule.
--
--   **Formalization Note** Plays are the `IsValidPrefix` / `IsValidRun` sequences of the DCRule definition; parts 1–2 range over every valid prefix after which $i$ is unserved and (part 1) is the Divider or (part 2) is not. The others' behaviour is constrained only by Definition 4. Only agent $i$'s utility enters, since the others' choices are arbitrary. $d\ge1$ is non-atomicity, needed for part 1.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 15, §4, Theorem 1 i); p. 6 (meaning of "guarantees")

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule

namespace FairGuarantees.DivideChoose

/-- Theorem 1 i), p. 15: in the D&C_n rule, an agent `i` with utility `u ∈ D(Ω)` guarantees
`minMax(u; n)` (of the initial problem) by dividing with equipartitions and accepting exactly
the shares worth at least `minMax(u; n)`, whatever the other agents do:
1. whenever `i` is called to divide, an equipartition of the remaining manna among the
   remaining agents exists;
2. whenever `i` must report the shares he likes, some offered share is worth at least
   `minMax(u; n)`;
3. in every complete valid play in which `i` follows the strategy, the share `i` receives is
   worth at least `minMax(u; n)`. -/
theorem theorem_1_i {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) (i : Fin n) :
    (∀ run : List (DCStep d n), IsValidPrefix Ω run → FollowsMinMaxStrategy Ω u i run →
      i ∈ nextAgents run → (∀ b ∈ nextAgents run, i ≤ b) →
      ∃ P : Fin (nextAgents run).card → Set (E d),
        IsEquipartition Ω u (nextManna Ω run) (nextAgents run).card P) ∧
    (∀ run : List (DCStep d n), IsValidPrefix Ω run → FollowsMinMaxStrategy Ω u i run →
      i ∈ nextAgents run → ¬ (∀ b ∈ nextAgents run, i ≤ b) →
      ∀ P : Fin (nextAgents run).card → Set (E d),
        IsPartition Ω (nextManna Ω run) (nextAgents run).card P →
        ∃ r, minMax Ω u n ≤ u (P r)) ∧
    (∀ run : List (DCStep d n), IsValidRun Ω run → FollowsMinMaxStrategy Ω u i run →
      minMax Ω u n ≤ u (share run i)) := by sorry

end FairGuarantees.DivideChoose
