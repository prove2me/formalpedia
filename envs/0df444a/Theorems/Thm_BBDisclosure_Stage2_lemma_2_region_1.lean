-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_lemma_2_region_1
-- name    : BBDisclosure.Stage2.lemma_2_region_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:42.141549+00:00
-- url     : https://prove2.me/theorems/2db42401-fa7d-422d-bad5-4f967efcaf53
-- title:
--   Lemma 2, region 1, p. 8518 — the unique turf equilibria are the inner-solution prices
-- statement:
--   Fix the first-period share $x_1$ and segment beliefs $\tilde q_{ao},\tilde q_{bn}$ (A's old customers' beliefs about A and B) and $\tilde q_{an},\tilde q_{bo}$ (B's old customers' beliefs about A and B), all in $[0,1]$. Suppose $x_1$ lies in region 1:
--   $$\frac14+\frac{\tilde q_{ao}-\tilde q_{bn}}{4}<x_1<\frac34+\frac{\tilde q_{an}-\tilde q_{bo}}{4}.$$
--   Then
--   1. the price game on A's turf has exactly one Nash equilibrium,
--   $$p^*_{ao}=\frac{1+2x_1+\tilde q_{ao}-\tilde q_{bn}}{3},\qquad p^*_{bn}=\frac{4x_1-1+\tilde q_{bn}-\tilde q_{ao}}{3};$$
--   2. the price game on B's turf has exactly one Nash equilibrium,
--   $$p^*_{an}=\frac{3-4x_1+\tilde q_{an}-\tilde q_{bo}}{3},\qquad p^*_{bo}=\frac{3-2x_1+\tilde q_{bo}-\tilde q_{an}}{3}.$$
--
--   These are the second-stage prices from which every disclosure threshold and profit formula of the paper is derived. Lemma 1 (p. 8515), the uniform-disclosure benchmark, is the special case $\tilde q_{ao}=\tilde q_{an}=\tilde q_a$, $\tilde q_{bn}=\tilde q_{bo}=\tilde q_b$, since both regimes use the same turf games.
--
--   **Formalization Note** The paper's "three equilibria can arise" is read as "in region 1 the equilibrium is the one given", stated as an equivalence (existence and uniqueness). Prices range over the nonnegative reals and shares are clamped to the turf. Region 1 already forces $0<x_1<1$.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8518, Lemma 2, region 1 (and p. 8515, Lemma 1, region 1)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem lemma_2_region_1 (x1 uao ubn uan ubo : ℝ)
    (huao : uao ∈ Set.Icc (0 : ℝ) 1) (hubn : ubn ∈ Set.Icc (0 : ℝ) 1)
    (huan : uan ∈ Set.Icc (0 : ℝ) 1) (hubo : ubo ∈ Set.Icc (0 : ℝ) 1)
    (hx : x1 ∈ Set.Ioo (1 / 4 + (uao - ubn) / 4) (3 / 4 + (uan - ubo) / 4)) :
    (∀ p : ℝ × ℝ, IsTurfNashA x1 uao ubn p ↔
      p = ((1 + 2 * x1 + uao - ubn) / 3, (4 * x1 - 1 + ubn - uao) / 3)) ∧
    (∀ p : ℝ × ℝ, IsTurfNashB x1 uan ubo p ↔
      p = ((3 - 4 * x1 + uan - ubo) / 3, (3 - 2 * x1 + ubo - uan) / 3)) := by sorry

end BBDisclosure.Stage2
