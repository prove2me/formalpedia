-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_anchor_profile_eligible
-- name    : ConsistentSubmodular.AtomicProfile.high_anchor_profile_eligible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:18.681599+00:00
-- url     : https://prove2.me/theorems/74e64a3f-7281-4aec-9c1e-b511f8d5d6c6
-- title:
--   Profile eligibility from a high anchor ($d_h \ge 33/40$, $1 \le q \le 2$)
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h \le s$ be stages with $d_h \ge \tfrac{33}{40}$, and suppose $h$ has strong credit: $B_h - 1 \ge \tfrac12$ or $1 - d_h \le (B_h-1)\bigl(1-(B_h-1)\bigr)$. Let $q$ be real with $1 \le q \le 2$, $d_h - r_{h,s} > 0$, and raw ratio $\rho(h,s) = q$, where The raw ratio is $\rho(h,t) = \dfrac{4(d_t - r_{h,t}) - (B_t - d_h) - 3(1-d_h)}{d_h - r_{h,t}}$. Then the actual eligibility is nonnegative:
--   $$0 \le E_h(q,s) = 4d_h - 3 - q(d_h - d_s) - \bigl(q - \tfrac{q^2}{4}\bigr) r_{h,s}.$$
--   It shows that, from a sufficiently high anchor with strong credit, an attaining row with ratio in $[1,2]$ is always eligible, which is used in the relay and rollback analyses of the selector.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ProfileEligibility.lean#L32-L50 (`ConsistentSubmodular.AtomicProfile.high_anchor_profile_eligible`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.high_anchor_profile_eligible (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 ≤ P.actualEligibility h q s := by sorry
