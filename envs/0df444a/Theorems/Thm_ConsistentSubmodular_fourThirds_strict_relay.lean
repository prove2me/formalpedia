-- Prove2me | Theorems.Thm_ConsistentSubmodular_fourThirds_strict_relay
-- name    : ConsistentSubmodular.fourThirds_strict_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:09.058646+00:00
-- url     : https://prove2.me/theorems/9567b893-a19b-42bf-a868-f24093d3e9e7
-- title:
--   Four-thirds relay — strict safety of the relay edge
-- statement:
--   Let $d,p,\delta,w,b,q$ be reals with $0 \le d < \tfrac14$, $p \ge 0$, $\delta \ge 0$, $w \ge 0$, $\delta + w \le 1 - d$, $\delta + w > 0$, $b \ge p + d$, $\tfrac43 \le q \le 2$. Assume
--
--   1. (credit) $p \ge \tfrac12$ or $d \le p(1-p)$,
--   2. (attainment) $(3-q)\,w = q\delta + b + 3d$,
--   3. (failure) $q(b + w) < 2(1-d)q - 3(1-4d)$.
--
--   Then for every real $z$ with $0 \le z \le 1$,
--   $$\tfrac34 < (1-d) - \delta z - (1-d-\delta-w)\,z(1-z).$$
--   The four-thirds relay combines its deficient-baseline boundary argument with the general credit-to-determinant argument at larger baselines; the statement is the scalar form of the strict safety of a relay edge.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayProfiles.lean#L10-L56 (`ConsistentSubmodular.fourThirds_strict_relay`)

import Mathlib

theorem ConsistentSubmodular.fourThirds_strict_relay (d p δ w b q : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (_hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hatt : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : q * (b + w) < 2 * (1 - d) * q - 3 * (1 - 4 * d)) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by sorry
