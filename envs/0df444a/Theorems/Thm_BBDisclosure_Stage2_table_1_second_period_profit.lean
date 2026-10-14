-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_table_1_second_period_profit
-- name    : BBDisclosure.Stage2.table_1_second_period_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:44.044511+00:00
-- url     : https://prove2.me/theorems/081234c9-b7bf-4438-91c2-549a93c49cad
-- title:
--   Table 1, row Second-period profit (E(π*_a2)), p. 8517 — uniform and BBD columns
-- statement:
--   Let $0<c<5/36$ and $x_1=1/2$. In every second-period equilibrium under uniform disclosure, firm A's ex ante second-period profit is
--   $$E(\pi^*_{a2})=\frac{232-891c}{729}-\frac{16+54c-10206c^2}{729\sqrt{1+27c}},$$
--   and in every second-period equilibrium under behavior-based disclosure it is
--   $$E(\pi^*_{a2})=\frac{244-891c}{729}-\frac{2+3c-252c^2}{54\sqrt{1+12c}}-\frac{2+27c-20412c^2}{1458\sqrt{1+108c}}.$$
--
--   Comparing the two columns gives Proposition 1(c).
--
--   **Formalization Note** Table 1 reports the symmetric equilibrium, whose first-period share is $x_1=1/2$; the row is stated at that share. The paper reports firm A by symmetry; the theorem is stated for A.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8517, Table 1, row Second-period profit (E(π*_a2))

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem table_1_second_period_profit (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36)
    (u : ProfileU) (hu : IsStage2EqU c (1 / 2) u)
    (e : ProfileBBD) (he : IsStage2EqBBD c (1 / 2) e) :
    exAnteA_U c (1 / 2) u = (232 - 891 * c) / 729
      - (16 + 54 * c - 10206 * c ^ 2) / (729 * Real.sqrt (1 + 27 * c)) ∧
    exAnteA_BBD c (1 / 2) e = (244 - 891 * c) / 729
      - (2 + 3 * c - 252 * c ^ 2) / (54 * Real.sqrt (1 + 12 * c))
      - (2 + 27 * c - 20412 * c ^ 2) / (1458 * Real.sqrt (1 + 108 * c)) := by sorry

end BBDisclosure.Stage2
