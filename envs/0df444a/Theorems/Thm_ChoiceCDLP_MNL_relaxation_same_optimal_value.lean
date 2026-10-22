-- Prove2me | Theorems.Thm_ChoiceCDLP_MNL_relaxation_same_optimal_value
-- name    : ChoiceCDLP.MNL.relaxation_same_optimal_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:58:46.821674+00:00
-- url     : https://prove2.me/theorems/f5b1da8d-ef8d-4b86-8960-c08bd8dad864
-- title:
--   Claim (17), proof of Proposition 6 — the box relaxation of the MNL offer-set problem has the same optimal value
-- statement:
--   Let $\iota$ be a finite consideration set, $v_j > 0$ the MNL preference weights, $v_0 \ge 0$ the no-purchase weight and $w_j \in \mathbb{R}$ arbitrary scores. Write $f(S) = \sum_{j\in S} w_j v_j / (\sum_{j\in S} v_j + v_0)$ for offer sets $S \subseteq \iota$ and $h(z) = \sum_j w_j z_j / (\sum_j z_j + v_0)$ for $z$ in the box $\mathcal{D} = \prod_j [0, v_j]$. Then both maxima exist and coincide:
--   $$\max_{z \in \mathcal{D}} h(z) \;=\; \max_{S \subseteq \iota} f(S).$$
--   Precisely: there is a number $M$ that is the greatest element of $h(\mathcal{D})$ and also the greatest element of $\{ f(S) : S \subseteq \iota\}$.
--
--   The claim reduces the combinatorial problem (14) to a continuous problem over a box, where the structure of the objective (a ratio of linear functions) can be exploited. It is the first step of the paper's proof of Proposition 6.
--
--   **Formalization Note.** Existence of the maximum over $\mathcal{D}$ is part of the conclusion (`IsGreatest`), so no `sSup` junk value can arise. The case $v_0 = 0$ is included, with $h(0) = f(\emptyset) = 0$ by Lean's $0/0 = 0$ (the paper's convention $h(0) := 0$). The paper's display (17) writes the summation index as $l \in C_l$; this is a typo for $j \in C_l$ and is formalized as intended.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 309, Appendix, proof of Proposition 6, claim (17)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_ChoiceCDLP_MNL_relaxedObjective

namespace ChoiceCDLP.MNL

/-- Claim (17) in the proof of Proposition 6 (p. 309): the relaxation of the 0/1 offer
problem (14) to the box `𝒟 = ∏_j [0, v_j]` has the same optimal value. Both maxima are
attained, and they are equal: there is one number `M` that is the greatest value of `h` on
`𝒟` and also the greatest value of `f(S)` over all offer sets `S`. -/
theorem relaxation_same_optimal_value {ι : Type*} [Fintype ι] (v w : ι → ℝ) (v₀ : ℝ)
    (hv : ∀ j, 0 < v j) (hv₀ : 0 ≤ v₀) :
    ∃ M : ℝ, IsGreatest (relaxedObjective w v₀ '' Set.Icc 0 v) M ∧
      IsGreatest (Set.range (mnlObjective v w v₀)) M := by sorry

end ChoiceCDLP.MNL
