-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_theorem_2
-- name    : BellDetEff.TwoParty.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:46.747748+00:00
-- url     : https://prove2.me/theorems/6ef5c068-aec3-458d-b5f8-0370dabea009
-- title:
--   Theorem 2 — in two-party Bell tests with M_A and M_B inputs, η*_NS ≤ (M_A + M_B − 2)/(M_A M_B − 1)
-- statement:
--   Consider two-party Bell tests in which A has $M_A$ inputs and B has $M_B$ inputs, with $M_A,M_B\ge 1$ and $M_AM_B\ge 2$. Let $\eta^*_{NS}(M_A,M_B)$ be the efficiency bound of eq. (A3): the infimum, over all no-signaling behaviours with these inputs and arbitrary finite output alphabets, of the largest detector efficiency at which the behaviour can still be simulated by a local hidden variable model. Then
--   $$\eta^*_{NS}(M_A,M_B)\le\frac{M_A+M_B-2}{M_AM_B-1}.$$
--
--   Together with the matching lower bound of Theorem 1 (obtained in the paper by citing a local model of Massar and Pironio), this shows that $(M_A+M_B-2)/(M_AM_B-1)$ is the exact detection-efficiency threshold for demonstrating the nonlocality of the maximally nonlocal no-signaling theory with two parties. In particular it tends to $0$ as the number of inputs grows.
--
--   **Formalization Note** The hypotheses $M_A,M_B\ge 1$ and $M_AM_B\ge 2$ are implicit in the paper. At $M_A=M_B=1$ the right-hand side is $0/0$, which Lean evaluates to $0$, and the claim would be false: with one input each, every behaviour is local and $e=1$. The bound is a real number, with no natural-number subtraction. $\eta^*_{NS}$ is the infimum over all output alphabets and all no-signaling behaviours, and local hidden variable models range over arbitrary probability spaces with measurable response functions.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 2, Theorem 2, eq. (5)

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency

namespace BellDetEff.TwoParty

/-- Theorem 2 (Cao–Peng, arXiv:1607.04350v1, p. 2, eq. (5)): in two-party Bell tests with `MA`
and `MB` inputs, `η*_NS ≤ (MA + MB − 2)/(MA MB − 1)`. -/
theorem theorem_2 (MA MB : ℕ) (hA : 1 ≤ MA) (hB : 1 ≤ MB) (hAB : 2 ≤ MA * MB) :
    etaStarNS MA MB ≤ ((MA : ℝ) + MB - 2) / ((MA : ℝ) * MB - 1) := by sorry

end BellDetEff.TwoParty
