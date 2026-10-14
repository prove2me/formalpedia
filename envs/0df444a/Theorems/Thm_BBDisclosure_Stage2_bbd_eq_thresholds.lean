-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_bbd_eq_thresholds
-- name    : BBDisclosure.Stage2.bbd_eq_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:50.809471+00:00
-- url     : https://prove2.me/theorems/078f64d3-1246-40af-b4f6-feb7f37ba384
-- title:
--   p. 8519, after (17) — at x₁ = 1/2, q̂*_ao = q̂*_bo = √(1+12c) − 1 and q̂*_an = q̂*_bn = (√(1+108c) − 1)/3
-- statement:
--   Under behavior-based disclosure, let $0<c<5/36$ and let the first-period share be the symmetric equilibrium share $x_1=1/2$. In every second-period equilibrium
--   $$\hat q^*_{ao}=\hat q^*_{bo}=\sqrt{1+12c}-1,\qquad \hat q^*_{an}=\hat q^*_{bn}=\frac{\sqrt{1+108c}-1}{3}.$$
--
--   These are the BBD entries of Table 1 for the own- and new-customer thresholds; comparing them gives Proposition 1(a).
--
--   **Formalization Note** The paper states this for the symmetric first-period equilibrium, whose share is $x_1=1/2$ (Table 1; (16), (17)); the first period is the subject of the companion mission. No region hypothesis is needed at $x_1=1/2$.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8519, sentence after (17); Table 1 rows Own-customer threshold and New-customer threshold

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem bbd_eq_thresholds (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileBBD)
    (he : IsStage2EqBBD c (1 / 2) e) :
    e.qao = Real.sqrt (1 + 12 * c) - 1 ∧ e.qbo = Real.sqrt (1 + 12 * c) - 1 ∧
      e.qan = (Real.sqrt (1 + 108 * c) - 1) / 3 ∧
      e.qbn = (Real.sqrt (1 + 108 * c) - 1) / 3 := by sorry

end BBDisclosure.Stage2
