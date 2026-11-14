-- Prove2me | Theorems.Thm_ConsistentSubmodular_fourThirds_low_baseline_relay
-- name    : ConsistentSubmodular.fourThirds_low_baseline_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:04.275209+00:00
-- url     : https://prove2.me/theorems/1ec252f9-9109-4759-a0a0-08b1d4164029
-- title:
--   Four-thirds relay — returning from the formal boundary to a strictly failed row
-- statement:
--   Let $p,d,q,\delta,w,b,z$ be reals with $0 < p \le \tfrac12$, $\tfrac p2 \le d < \tfrac14$, $d \le p(1-p)$, $\tfrac43 \le q \le 2$, $\delta \ge 0$, $b \ge p + d$, $0 \le z \le 1$. Assume
--
--   1. (attainment) $(3-q)\,w = q\delta + b + 3d$,
--   2. (failure) $b + w < 2(1-d) - \dfrac{3(1-4d)}{q}$.
--
--   Then
--   $$0 < \tfrac14 - d - \delta z - (1 - d - \delta - w)\,z(1-z).$$
--   Starting from the safe formal boundary row, the strictly failed source row is reached by affine interpolation in the coordinates $(\delta, b)$, and the margin stays strictly positive. This handles the case of a deficient baseline in the four-thirds relay.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/FourThirdsBoundary.lean#L255-L326 (`ConsistentSubmodular.fourThirds_low_baseline_relay`)

import Mathlib

theorem ConsistentSubmodular.fourThirds_low_baseline_relay (p d q δ w b z : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4)
    (hcredit : d ≤ p * (1 - p)) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hratio : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : b + w < 2 * (1 - d) - 3 * (1 - 4 * d) / q)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < 1 / 4 - d - δ * z - (1 - d - δ - w) * z * (1 - z) := by sorry
