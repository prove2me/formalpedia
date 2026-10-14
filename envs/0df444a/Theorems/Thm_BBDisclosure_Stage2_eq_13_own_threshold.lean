-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_eq_13_own_threshold
-- name    : BBDisclosure.Stage2.eq_13_own_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:44.850235+00:00
-- url     : https://prove2.me/theorems/0dd0f116-ce4e-43af-85f0-a0259dd879c4
-- title:
--   (13), p. 8518 — the BBD own-customer threshold q̂*_ao = (√(216x₁c + (1 + 4x₁)²) − 4x₁ − 1)/3
-- statement:
--   Under behavior-based disclosure, let $0<c<5/36$ and $0<x_1<1$, and take any second-period equilibrium whose threshold $\hat q_{bn}$ for B's disclosure to A's old customers satisfies $1/2-\hat q_{bn}/8<x_1$, so that every belief pair on A's turf lies in region 1. Then A's disclosure threshold for its own customers is
--   $$\hat q^*_{ao}=\frac{\sqrt{216x_1c+(1+4x_1)^2}-4x_1-1}{3}.$$
--
--   The threshold balances the cost $x_1c$ of disclosing to A's turf against the revenue gain on that turf alone.
--
--   **Formalization Note** The paper says "in region 1"; only the turf-$[0,x_1]$ half of the support window, $1/2-\hat q_{bn}/8<x_1$, concerns this threshold, and it is the hypothesis used.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8518, (13)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem eq_13_own_threshold (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36)
    (hx : x1 ∈ Set.Ioo (0 : ℝ) 1) (e : ProfileBBD)
    (he : IsStage2EqBBD c x1 e) (hreg : 1 / 2 - e.qbn / 8 < x1) :
    e.qao = (Real.sqrt (216 * x1 * c + (1 + 4 * x1) ^ 2) - 4 * x1 - 1) / 3 := by sorry

end BBDisclosure.Stage2
