-- Prove2me | Theorems.Thm_BBDisclosure_Total_table_1_total_profits
-- name    : BBDisclosure.Total.table_1_total_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:28.646855+00:00
-- url     : https://prove2.me/theorems/e9ffaa9c-2105-44ac-93dd-368606abd3bf
-- title:
--   Table 1, row Total profits $(\Pi^*_a)$, p. 8517 — equilibrium two-period profits under uniform disclosure and under BBD
-- statement:
--   Let $0<c<5/36$. In every symmetric subgame-perfect equilibrium of the two-period game with uniform disclosure, both firms' total two-period profits equal
--
--   $$\Pi^*_a=\Pi^*_b=\frac{718-1134c}{729}-\frac{16-189c-10206c^2}{729\sqrt{1+27c}},$$
--
--   and in every symmetric subgame-perfect equilibrium of the game with behavior-based disclosure they equal
--
--   $$\Pi^*_a=\Pi^*_b=\frac{730-891c}{729}-\frac{1+24c+117c^2}{27\sqrt{1+12c}}-\frac{1-594c-29889c^2}{729\sqrt{1+108c}}.$$
--
--   Proposition 3(a) compares these two expressions.
--
--   **Formalization Note.** The uniform formula is Table 1's; the sentence on p. 8517 prints $\sqrt{1+72c}$ in the last denominator, a misprint (the Table 1 version is the sum of the first-period profit $\tfrac13(2-c+c/\sqrt{1+27c})$ and the second-period profit of Table 1). Firm B's equality is the paper's "$\Pi^*_a=\Pi^*_b$" (pp. 8517, 8519).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8517, Table 1, row Total profits (Π*_a); p. 8519, sentence after (17)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- Table 1, row "Total profits (Π*_a)", p. 8517 (with `Π*_a = Π*_b`, pp. 8517, 8519): the
equilibrium two-period profits of both firms under uniform disclosure and under behavior-based
disclosure. -/
theorem table_1_total_profits (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∀ s : SPE_U, IsSymSPE_U c s →
      totalA_U c s = (718 - 1134 * c) / 729
          - (16 - 189 * c - 10206 * c ^ 2) / (729 * Real.sqrt (1 + 27 * c)) ∧
      totalB_U c s = (718 - 1134 * c) / 729
          - (16 - 189 * c - 10206 * c ^ 2) / (729 * Real.sqrt (1 + 27 * c))) ∧
    (∀ s : SPE_BBD, IsSymSPE_BBD c s →
      totalA_BBD c s = (730 - 891 * c) / 729
          - (1 + 24 * c + 117 * c ^ 2) / (27 * Real.sqrt (1 + 12 * c))
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * Real.sqrt (1 + 108 * c)) ∧
      totalB_BBD c s = (730 - 891 * c) / 729
          - (1 + 24 * c + 117 * c ^ 2) / (27 * Real.sqrt (1 + 12 * c))
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * Real.sqrt (1 + 108 * c))) := by sorry

end BBDisclosure.Total
