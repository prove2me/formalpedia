-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_rbmw_strongly_truthful
-- name    : AlgMechDesign.Randomized.rbmw_strongly_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:36:15.729768+00:00
-- url     : https://prove2.me/theorems/7c649523-a15d-4eeb-95d5-f5ebfcff93d2
-- title:
--   Lemma 4.17 — the randomly biased min work mechanism is strongly truthful
-- statement:
--   For every number $k$ of tasks, the randomly biased min work mechanism (the uniform distribution over the biased min work mechanisms with $\beta = 4/3$ and $s \in \{1,2\}^k$) is universally strongly truthful:
--
--   1. for every $s \in \{1,2\}^k$, the biased min work mechanism with parameters $4/3$ and $s$ is truthful on positive types; and
--   2. for every agent $i$, every positive true type $t^i$ and every positive misreport $d^i \ne t^i$, there are $s$ and a positive declaration $d^{-i}$ of the other agent under which declaring $d^i$ gives agent $i$ strictly smaller utility than declaring $t^i$.
--
--   Truthfulness is required for every outcome of the coin tosses, not in expectation.
--
--   **Formalization Note** Given part 1, part 2 says exactly that truth-telling is the only universally dominant strategy (Definition 16); the support of the uniform distribution is all of $\{1,2\}^k$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 182, Lemma 4.17

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Lemma 4.17: for every number `k` of tasks, the randomly biased min work mechanism
(`β = 4/3`, `s` uniform on `{1, 2}ᵏ`, full support) is universally strongly truthful. -/
theorem rbmw_strongly_truthful {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay := by sorry

end AlgMechDesign.Randomized
