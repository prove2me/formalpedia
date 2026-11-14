-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_fourThirds_profile_relay
-- name    : ConsistentSubmodular.AtomicProfile.fourThirds_profile_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:20.196977+00:00
-- url     : https://prove2.me/theorems/93d2a8a8-8600-421b-be87-9454e2c44380
-- title:
--   Four-thirds relay for atomic profiles
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h < s$ be stages with $d_h > \tfrac34$ and strong credit at $h$: $h$ has strong credit: $B_h - 1 \ge \tfrac12$ or $1 - d_h \le (B_h-1)\bigl(1-(B_h-1)\bigr)$. Let $\tfrac43 \le q \le 2$ with $d_h - r_{h,s} > 0$ and raw ratio $\rho(h,s) = q$, where The raw ratio is $\rho(h,t) = \dfrac{4(d_t - r_{h,t}) - (B_t - d_h) - 3(1-d_h)}{d_h - r_{h,t}}$. Assume the failure condition
--   $$q\,(B_s - d_h) < 2d_hq - 3(4d_h - 3).$$
--   Then all of the following hold:
--
--   1. the edge from $h$ to $s$ is pessimistically safe: for every $z \in [0,1]$,
--   $$\tfrac34 \le d_h - (d_h - d_s)z - r_{h,s}\,z(1-z);$$
--   2. $d_s > \tfrac34$;
--   3. $s$ has strong credit.
--
--   It is the profile-level relay step for parameters in $[\tfrac43, 2]$: a failed row yields a safe edge to a new high anchor retaining strong credit, so the access certificate can be extended.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayProfiles.lean#L72-L99 (`ConsistentSubmodular.AtomicProfile.fourThirds_profile_relay`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.fourThirds_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (3 : ℝ) / 4 < P.designated h) (hcredit : P.StrongCredit h)
    (q : ℝ) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    P.PessimisticSafeEdge h s ∧ (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by sorry
