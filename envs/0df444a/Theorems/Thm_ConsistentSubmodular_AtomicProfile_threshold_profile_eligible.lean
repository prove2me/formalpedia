-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_threshold_profile_eligible
-- name    : ConsistentSubmodular.AtomicProfile.threshold_profile_eligible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:27.586604+00:00
-- url     : https://prove2.me/theorems/f680d3b5-407c-4526-bd20-4a2e4a7707f4
-- title:
--   Profile eligibility above the threshold anchor $d_h \ge 1281/1600$
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h \le s$ be stages with $d_h \ge \tfrac{1281}{1600}$, and suppose $h$ has strong credit: $B_h - 1 \ge \tfrac12$ or $1 - d_h \le (B_h-1)\bigl(1-(B_h-1)\bigr)$. Let $0 < q \le 1$ with $d_h - r_{h,s} > 0$ and raw ratio $\rho(h,s) = q$, where The raw ratio is $\rho(h,t) = \dfrac{4(d_t - r_{h,t}) - (B_t - d_h) - 3(1-d_h)}{d_h - r_{h,t}}$. Then the actual eligibility is strictly positive:
--   $$0 < E_h(q,s) = 4d_h - 3 - q(d_h - d_s) - \bigl(q - \tfrac{q^2}{4}\bigr) r_{h,s}.$$
--   The constant $\tfrac{1281}{1600}$ is the threshold anchor below which the low rollback case must be analysed; above it, attaining rows with small ratio are strictly eligible.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ProfileEligibility.lean#L52-L69 (`ConsistentSubmodular.AtomicProfile.threshold_profile_eligible`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.threshold_profile_eligible (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (1281 : ℝ) / 1600 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 < P.actualEligibility h q s := by sorry
