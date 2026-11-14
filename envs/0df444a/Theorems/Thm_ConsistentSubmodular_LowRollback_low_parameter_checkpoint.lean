-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_low_parameter_checkpoint
-- name    : ConsistentSubmodular.LowRollback.low_parameter_checkpoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:19.24474+00:00
-- url     : https://prove2.me/theorems/bdb5fe79-57c8-4426-8716-397f244a6577
-- title:
--   Low rollback — a checkpoint certificate in the low-child branch
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ and let $h$ be a stage with a selector state: $\tfrac34 < d_h < 1$, a safe access certificate for $h$ (a $\tfrac34$-safe polygonal path from vertex $0$ to vertex $h$ with at most $h$ pieces), strong credit at $h$, and a relay history whose parameter $k$ satisfies $1 \le k < 3$. Let $\rho(h,t)$ denote the raw ratio and $E_h(q,t)$ the actual eligibility, and let $q = \rho_{\max}(h)$ be the raw envelope of $h$, the maximum of $0$ and of $\rho(h,t)$ over later active stages $t > h$ (active meaning $b_t < 3d_t$). Assume
--
--   1. $k \ge \tfrac43$ (the history parameter),
--   2. $d_h < \tfrac{1281}{1600}$,
--   3. $0 < q \le 1$,
--   4. $E_h(q,t) < 0$ for every active stage $t > h$.
--
--   Then a checkpoint certificate for $P$ exists: a point $x$ of the simplex supported on at most two stages with $\tfrac34 B_t \le \mathrm{value}_t(x)$ for every stage $t$, together with a $\tfrac34$-safe entry path from vertex $0$ to $x$, a safe exit path from $x$ to vertex $m$ (at level $\tfrac34 B_m$ with respect to stage $m$), using in total at most $m+3$ affine pieces.
--
--   In the low-child branch, rollback returns the retained parent's pair; all numerical source bounds and the chronology of the attaining row are derived from the original profile and history, and the safe root entry is preserved.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollback.lean#L50-L188 (`ConsistentSubmodular.LowRollback.low_parameter_checkpoint`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.low_parameter_checkpoint (P : AtomicProfile m aCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (state : SelectorState P h)
    (hparent : 4 / 3 ≤ state.history.parameter)
    (hanchor : P.designated h < 1281 / 1600)
    (hq0 : 0 < P.rawEnvelope h) (hq1 : P.rawEnvelope h ≤ 1)
    (hno : ∀ t, h < t → P.Active t → P.actualEligibility h (P.rawEnvelope h) t < 0) :
    Nonempty (CheckpointCertificate P) := by sorry
