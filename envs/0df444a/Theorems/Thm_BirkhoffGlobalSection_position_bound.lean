-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_position_bound
-- name    : BirkhoffGlobalSection.position_bound
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:10:13.156216+00:00
-- url     : https://prove2.me/theorems/5d0db569-5b6c-40bb-b56e-3b0fe70eb352
-- title:
--   Lemma 4.1 — Levi-Civita position bound
-- statement:
--   Let $0\leq\mu\leq1/2$ and $c\geq2.1$. Every point $(z,w)$ of the selected Levi-Civita energy component satisfies
--
--   $$
--   2|z|^2\leq\frac35.
--   $$
--
--   This is the “in particular” conclusion of Joung--van Koert, Lemma 4.1, and confines the regularized position coordinate for the later curvature calculation.
-- source:
--   Joung--van Koert, Lemma 4.1, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The `2|z|² ≤ 3/5` consequence of Joung--van Koert, Lemma 4.1. -/
theorem position_bound (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    2 * zNormSq s ≤ 3 / 5 := by sorry

end BirkhoffGlobalSection
