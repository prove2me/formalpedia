-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_momentum_bound
-- name    : BirkhoffGlobalSection.momentum_bound
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:10:29.633385+00:00
-- url     : https://prove2.me/theorems/7105194e-43a7-427e-bc8e-ea6e2e9e1680
-- title:
--   Lemma 4.2 — Levi-Civita momentum bound
-- statement:
--   Let $0\leq\mu\leq1/2$ and $c\geq2.1$. Every point $(z,w)$ of the selected Levi-Civita energy component satisfies
--
--   $$
--   |w|\leq2.
--   $$
--
--   This is Joung--van Koert, Lemma 4.2. Together with the position estimate, it confines the component to the compact box used by the validated curvature computation.
-- source:
--   Joung--van Koert, Lemma 4.2, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Joung--van Koert, Lemma 4.2. -/
theorem momentum_bound (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    Real.sqrt (wNormSq s) ≤ 2 := by sorry

end BirkhoffGlobalSection
