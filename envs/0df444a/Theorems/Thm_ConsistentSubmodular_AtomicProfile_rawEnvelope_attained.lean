-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
-- name    : ConsistentSubmodular.AtomicProfile.rawEnvelope_attained
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:59.327648+00:00
-- url     : https://prove2.me/theorems/514f0fe4-bf19-4723-a500-29add1bb2dd3
-- title:
--   The positive raw envelope is attained by a genuine later active row
-- statement:
--   Let $P$ be an atomic profile on stages $0,\dots,m$: finitely many atoms with weights, pools and label sets, from which the baseline $L_t$, the residuals $r_i(t)$, the designated values $A_t=r_t(t)$ and the benchmark $P_t=L_t+A_t$ are defined. A stage $t$ is active when $L_t<3A_t$, and the later active stages of $h$ are those $t>h$ that are active. For stages $h<t$ put
--   $$N_{h,t}=4\big(A_t-r_h(t)\big)-\big(P_t-A_h\big)-3\big(1-A_h\big),\qquad \rho_{h,t}=\frac{N_{h,t}}{A_h-r_h(t)},$$
--   and let the raw envelope be $\max\big(\{0\}\cup\{\rho_{h,t}: t\text{ later active for }h\}\big)$.
--
--   Fix a stage $h$ and suppose the raw envelope of $h$ is strictly positive. Then there is a stage $t$ that is later active for $h$, with
--
--   $$A_h-r_h(t)>0\qquad\text{and}\qquad \rho_{h,t}=\text{(raw envelope of }h).$$
--
--   A positive finite envelope is thus attained by an actual later active row with a positive denominator; no omitted zero row can be the attainer.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Envelope.lean#L80-L96 (`ConsistentSubmodular.AtomicProfile.rawEnvelope_attained`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.rawEnvelope_attained (h : Fin (m + 1)) (hq : 0 < P.rawEnvelope h) :
    ∃ t, t ∈ P.laterActive h ∧ 0 < P.designated h - P.residual h t ∧
      P.rawRatio h t = P.rawEnvelope h := by sorry
