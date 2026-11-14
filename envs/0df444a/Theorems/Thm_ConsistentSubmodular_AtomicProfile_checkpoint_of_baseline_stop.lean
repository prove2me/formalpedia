-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_checkpoint_of_baseline_stop
-- name    : ConsistentSubmodular.AtomicProfile.checkpoint_of_baseline_stop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:52.096837+00:00
-- url     : https://prove2.me/theorems/301fc9c7-04a3-4aac-9998-4135bb252e6b
-- title:
--   Checkpoint certificate from a baseline stop
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h$ be a stage with $d_h > \tfrac34$ and let an access certificate for $h$ be given (a $\tfrac34$-safe polygonal path from vertex $0$ to vertex $h$ with at most $h$ pieces). Let $\rho_{\max}(h)$ be the raw envelope at $h$: the maximum of $0$ and of the raw ratios $\rho(h,t)$ over later active stages $t > h$ (active meaning $b_t < 3d_t$). Assume
--
--   1. $3(1-d_h) \le b_h$ (baseline stop),
--   2. $1 \le \rho_{\max}(h) \le \tfrac32$.
--
--   Then a checkpoint certificate for $P$ exists: a point $x$ of the simplex supported on at most two stages with $\tfrac34 B_t \le \mathrm{value}_t(x)$ for every stage $t$, a $\tfrac34$-safe entry path from vertex $0$ to $x$, a safe exit path from $x$ to vertex $m$ (at level $\tfrac34 B_m$ with respect to stage $m$), and at most $m+3$ affine pieces in total.
--
--   It is the termination step of the selector construction: when the baseline is already large at an anchor whose envelope lies in $[1,\tfrac32]$, the certificate is completed.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ProfileEligibility.lean#L71-L98 (`ConsistentSubmodular.AtomicProfile.checkpoint_of_baseline_stop`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.checkpoint_of_baseline_stop (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 < P.designated h)
    (access : AccessCertificate P h)
    (hL : 3 * (1 - P.designated h) ≤ P.baseline h)
    (hq1 : 1 ≤ P.rawEnvelope h) (hq3 : P.rawEnvelope h ≤ 3 / 2) :
    Nonempty (CheckpointCertificate P) := by sorry
