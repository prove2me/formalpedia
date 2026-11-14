-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_middle_parameter_checkpoint
-- name    : ConsistentSubmodular.AtomicProfile.middle_parameter_checkpoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:32.67555+00:00
-- url     : https://prove2.me/theorems/8608c35f-304a-4efc-af7b-0277791e841e
-- title:
--   Middle rollback retains access and credit — checkpoint certificate exists
-- statement:
--   Let $P$ be a canonical atomic profile on stages $0,\dots,m$ (finitely many weighted atoms with pools and label sets; $A_t$ denotes the designated mass, $B_t$ the baseline, $P_t=B_t+A_t$ the benchmark of stage $t$). Let $h$ be a stage carrying a selector state $S$ (high anchor $A_h>\tfrac34$, $A_h<1$, an access certificate and strong credit at $h$, and a relay history). Let $q_h$ be the raw envelope at $h$: the maximum of $0$ and of the raw ratios of all later active stages. Assume
--
--   1. $1\le q_h<\tfrac43$;
--   2. $A_h<\tfrac{33}{40}$;
--   3. $B_h<3(1-A_h)$;
--   4. (no eligible later row) for every active $t>h$ with actual eligibility $\;4A_h-3-q_h(A_h-A_t)-(q_h-q_h^2/4)\,r_{h,t}\ge 0$,
--   $$q_h\,(P_t-A_h)<2A_hq_h-3(4A_h-3).$$
--
--   Then a checkpoint certificate for $P$ exists: a point $p$ of the simplex with at most two nonzero weights, value at least $\tfrac34P_t$ at every stage $t$, together with a safe entry path from $\delta_0$ and a safe exit path to $\delta_m$, having at most $m+3$ pieces in total.
--
--   In the selector procedure this is the middle-rollback exit: when the envelope parameter lies in $[1,4/3)$ and the anchor is not too high, the attaining parent's access and failed credit history yield a certificate directly.
--
--   **Formalization Note**: the conclusion is `Nonempty (CheckpointCertificate P)`, the certificate being data that bundles all of the properties above.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleRollback.lean#L15-L154 (`ConsistentSubmodular.AtomicProfile.middle_parameter_checkpoint`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)
set_option maxHeartbeats 1200000

theorem ConsistentSubmodular.AtomicProfile.middle_parameter_checkpoint (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq1 : 1 ≤ P.rawEnvelope h)
    (hq4 : P.rawEnvelope h < (4 : ℝ) / 3) (hA : P.designated h < (33 : ℝ) / 40)
    (hL : P.baseline h < 3 * (1 - P.designated h))
    (hno : ∀ t, h < t → P.Active t → 0 ≤ P.actualEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h)<
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3)) :
    Nonempty (CheckpointCertificate P) := by sorry
