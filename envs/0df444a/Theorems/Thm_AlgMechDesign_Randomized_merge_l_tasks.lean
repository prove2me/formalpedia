-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_merge_l_tasks
-- name    : AlgMechDesign.Randomized.merge_l_tasks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:40:17.260857+00:00
-- url     : https://prove2.me/theorems/d5622818-2501-4cf7-b821-51cac8c25819
-- title:
--   Claim 4.19, part 5 — merging two randomly allocated l-tasks can only increase the expected make-span
-- statement:
--   Two agents have finishing times $T^1, T^2 \ge 0$ under a fixed allocation $Y$ of all tasks but two, $a$ and $b$. Agent $i$ needs $t^i_a \ge 0$ for $a$ and $t^i_b \ge 0$ for $b$. Let $t_{Y,a,b}$ be the expected make-span when $a$ and $b$ are each given to agent 1 or agent 2 independently with probability $1/2$, and $t_{Y,c}$ the expected make-span when they are replaced by one task $c$ with $t^i_c = t^i_a + t^i_b$ given to either agent with probability $1/2$. Then $t_{Y,a,b} \le t_{Y,c}$, that is,
--   $$
--   \tfrac14\Big(\max(T^1 + t^1_a + t^1_b,\ T^2) + \max(T^1 + t^1_a,\ T^2 + t^2_b) + \max(T^1 + t^1_b,\ T^2 + t^2_a) + \max(T^1,\ T^2 + t^2_a + t^2_b)\Big)
--   \le \tfrac12\Big(\max(T^1 + t^1_a + t^1_b,\ T^2) + \max(T^1,\ T^2 + t^2_a + t^2_b)\Big).
--   $$
--
--   This is the step of the reduction of Lemma 4.18 to the four-task case of Fig. 2 that merges two l-tasks allocated by an optimal allocation to the same agent.
--
--   **Formalization Note** The statement is the explicit four-term average; the paper's w.l.o.g. ordering $t^i_a \ge t^i_b$ is not assumed.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 184, proof of Claim 4.19, part 5 (l-task case)

import Mathlib

namespace AlgMechDesign.Randomized

/-- Claim 4.19, part 5 (p. 184): with the other tasks fixed by an allocation `Y` giving
finishing times `T¹, T²`, allocating two l-tasks `a, b` (times `aⁱ, bⁱ` for agent `i`)
independently and uniformly at random yields an expected make-span `t_{Y,a,b}` at most that
`t_{Y,c}` of the single merged task `c` with `tⁱ_c = aⁱ + bⁱ` allocated uniformly at random. -/
theorem merge_l_tasks (T₁ T₂ a₁ a₂ b₁ b₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    (1 / 4 : ℝ) * (max (T₁ + a₁ + b₁) T₂ + max (T₁ + a₁) (T₂ + b₂) +
        max (T₁ + b₁) (T₂ + a₂) + max T₁ (T₂ + a₂ + b₂)) ≤
      (1 / 2 : ℝ) * (max (T₁ + a₁ + b₁) T₂ + max T₁ (T₂ + a₂ + b₂)) := by sorry

end AlgMechDesign.Randomized
