-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_bmw_strongly_truthful
-- name    : AlgMechDesign.Randomized.bmw_strongly_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:32:22.359643+00:00
-- url     : https://prove2.me/theorems/f6cfa448-50a5-482a-893f-402cb11e959c
-- title:
--   Lemma 4.15 — the biased min work mechanism is strongly truthful for all parameters
-- statement:
--   Consider task scheduling with two agents and $k$ tasks. For every real $\beta \ge 1$ and every bit vector $s \in \{1,2\}^k$, the biased min work mechanism with parameters $\beta$ and $s$ is strongly truthful on positive types:
--
--   1. for every positive declaration $d^{-i}$ of the other agent, every positive true type $t^i$ and every positive misreport $d^i$, agent $i$'s utility from declaring $t^i$ is at least that from declaring $d^i$;
--   2. for every positive $t^i$ and every positive $d^i \ne t^i$, there is a positive declaration $d^{-i}$ of the other agent under which declaring $d^i$ gives agent $i$ strictly smaller utility than declaring $t^i$.
--
--   Here agent $i$'s utility is the payment it receives minus $\sum_{j \in x^i} t^i_j$ over the tasks it is allocated. This lemma is the source of the universal truthfulness of the randomized mechanism.
--
--   **Formalization Note** "For all parameter values" is read as all $\beta \ge 1$ (the parameter range of Fig. 1) and all $s$; it is stated for every number $k$ of tasks.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 182, Lemma 4.15 (mechanism of Fig. 1)

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Lemma 4.15: for every parameter `β ≥ 1`, every bit vector `s ∈ {1, 2}ᵏ` and every number
`k` of tasks, the biased min work mechanism is strongly truthful on positive types. -/
theorem bmw_strongly_truthful {k : ℕ} (β : ℝ) (hβ : 1 ≤ β) (s : Fin k → Fin 2) :
    IsStronglyTruthful (bmwAlloc β s) (bmwPay β s) := by sorry

end AlgMechDesign.Randomized
