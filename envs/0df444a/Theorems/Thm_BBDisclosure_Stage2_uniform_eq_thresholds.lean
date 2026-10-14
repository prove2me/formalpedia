-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_uniform_eq_thresholds
-- name    : BBDisclosure.Stage2.uniform_eq_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:46.586582+00:00
-- url     : https://prove2.me/theorems/09e27ef7-0304-46bb-945d-21c70d33b518
-- title:
--   p. 8517, after (9) — at x₁ = 1/2 the uniform thresholds are q̂*_a = q̂*_b = 2(√(1+27c) − 1)/3
-- statement:
--   Under uniform disclosure, let $0<c<5/36$ and let the first-period share be the symmetric equilibrium share $x_1=1/2$. In every second-period equilibrium both firms' disclosure thresholds equal
--   $$\hat q^*_a=\hat q^*_b=\frac{2\big(\sqrt{1+27c}-1\big)}{3}.$$
--
--   This is the uniform-disclosure entry of Table 1 for the thresholds, the benchmark for Proposition 1.
--
--   **Formalization Note** The paper states this for the symmetric first-period equilibrium, whose share is $x_1=1/2$ (Table 1; (7), (9)); the first period is the subject of the companion mission. No region hypothesis is needed: at $x_1=1/2$ every belief pair on the support lies in region 1 as soon as the thresholds are positive, which the equilibrium forces when $c>0$.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8517, sentence after (9); Table 1 row Uniform threshold

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem uniform_eq_thresholds (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileU)
    (he : IsStage2EqU c (1 / 2) e) :
    e.qa = 2 * (Real.sqrt (1 + 27 * c) - 1) / 3 ∧
      e.qb = 2 * (Real.sqrt (1 + 27 * c) - 1) / 3 := by sorry

end BBDisclosure.Stage2
