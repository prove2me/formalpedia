-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_eq_4_uniform_threshold
-- name    : BBDisclosure.Stage2.eq_4_uniform_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:42.762951+00:00
-- url     : https://prove2.me/theorems/1b2d1ef0-be30-4829-abb9-953948ed3bc5
-- title:
--   (4), p. 8516 — the uniform disclosure threshold q̂*_a = (√(108c + (3 − 2x₁)²) + 2x₁ − 3)/3
-- statement:
--   Under uniform disclosure, let $0<c<5/36$ be the unit disclosure cost and $0<x_1<1$ the first-period share. Take any second-period equilibrium with thresholds $\hat q_a,\hat q_b$ such that every belief pair on the support lies in region 1, that is $1/2-\hat q_b/8<x_1<1/2+\hat q_a/8$. Then firm A's threshold is
--   $$\hat q^*_a=\frac{\sqrt{108c+(3-2x_1)^2}+2x_1-3}{3}.$$
--
--   The threshold balances the disclosure cost $c$ against the gain in expected revenue on both turfs from being believed to have quality $q_a$ rather than $\hat q_a/2$.
--
--   **Formalization Note** The paper says "in region 1"; since region 1 is a condition on $x_1$ and the realized beliefs, it is read as the support window above. The bound $c<5/36$ is the paper's standing assumption (p. 8515) and $c>0$ is implicit in a unit cost.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8516, (4)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem eq_4_uniform_threshold (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36)
    (hx : x1 ∈ Set.Ioo (0 : ℝ) 1) (e : ProfileU)
    (he : IsStage2EqU c x1 e) (hreg : SupportRegion1U x1 e) :
    e.qa = (Real.sqrt (108 * c + (3 - 2 * x1) ^ 2) + 2 * x1 - 3) / 3 := by sorry

end BBDisclosure.Stage2
