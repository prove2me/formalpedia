-- Prove2me | Theorems.Thm_BehrendWindows_small_range_bound
-- name    : BehrendWindows.small_range_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:48:39.372022+00:00
-- url     : https://prove2.me/theorems/0d5ab24e-436d-46a1-accf-aa23948adcca
-- title:
--   Small ranges: the bound is at most one
-- statement:
--   Let $C>0$ be real and $N,m\in\mathbb{N}$ with $N\ge 1$ and $N\le m^{C^2}$. Then
--
--   $$N\exp\!\Big(-C\sqrt{\log N\,\log m}\Big)\ \le\ 1 .$$
--
--   Consequently, in the range $N\le m^{C^2}$ the goal bound is met by a single point, and the construction is only needed when $m$ is small compared with $N$.
--
--   **Formalization Note** $m^{C^2}$ is the real power `Real.rpow`; for $m=0$ it equals $0$, so the hypothesis $N\le m^{C^2}$ forces $m\ge 1$.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 6

import Mathlib

namespace BehrendWindows

theorem small_range_bound (C : ℝ) (hC : 0 < C) (N m : ℕ) (hN : 1 ≤ N)
    (hNm : (N : ℝ) ≤ (m : ℝ) ^ (C ^ 2)) :
    (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log N * Real.log m)) ≤ 1 := by sorry

end BehrendWindows
