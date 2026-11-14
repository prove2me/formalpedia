-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_anchor_profile_relay
-- name    : ConsistentSubmodular.AtomicProfile.high_anchor_profile_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:03.381198+00:00
-- url     : https://prove2.me/theorems/03d01299-0dba-4821-88f7-978a40eabda7
-- title:
--   Relay for atomic profiles from a high anchor
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h < s$ be stages with $\tfrac{33}{40} \le d_h < 1$ and strong credit at $h$: $h$ has strong credit: $B_h - 1 \ge \tfrac12$ or $1 - d_h \le (B_h-1)\bigl(1-(B_h-1)\bigr)$. Let $q \ge 1$ be real with $d_h - r_{h,s} > 0$ and raw ratio $\rho(h,s) = q$, where The raw ratio is $\rho(h,t) = \dfrac{4(d_t - r_{h,t}) - (B_t - d_h) - 3(1-d_h)}{d_h - r_{h,t}}$. Assume the failure condition
--   $$q\,(B_s - d_h) < 2d_hq - 3(4d_h - 3).$$
--   Then all of the following hold:
--
--   1. the edge from $h$ to $s$ is pessimistically safe: for every $z \in [0,1]$,
--   $$\tfrac34 \le d_h - (d_h - d_s)z - r_{h,s}\,z(1-z);$$
--   2. $d_s > \tfrac34$;
--   3. $s$ has strong credit.
--
--   Compared with the four-thirds relay, the parameter range is unbounded above ($q \ge 1$) but the anchor must be at least $\tfrac{33}{40}$; it supports the relay step of the selector from high anchors.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayProfiles.lean#L101-L127 (`ConsistentSubmodular.AtomicProfile.high_anchor_profile_relay`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.high_anchor_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) (hA1 : P.designated h < 1)
    (hcredit : P.StrongCredit h) (q : ℝ) (hq : 1 ≤ q)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    P.PessimisticSafeEdge h s ∧ (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by sorry
