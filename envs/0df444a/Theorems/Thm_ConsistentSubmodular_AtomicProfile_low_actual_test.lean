-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_low_actual_test
-- name    : ConsistentSubmodular.AtomicProfile.low_actual_test
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:52.743445+00:00
-- url     : https://prove2.me/theorems/6882a38f-8368-4f89-832a-23f6cafeec97
-- title:
--   Low-parameter actual-eligibility test for the checkpoint constructor
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ (designated values $A_t$, residuals $R(i,t)$, benchmarks $B_t$), let $h$ be a stage, and let an access certificate for $(P,h)$ be given: a polygonal path from vertex $0$ to vertex $h$ with at most $h$ pieces, safe at level $\tfrac34$ for the stage-$0$ value of $P$. Call a stage $t$ active if its baseline is below $3A_t$, and let the envelope slack be
--   $$\mathrm{env}_{h,q}(t)=q\bigl[(A_h-A_t)+(A_t-R(h,t))\bigr]+(B_t-A_h)+3(1-A_h)-4\,(A_t-R(h,t)).$$
--
--   Assume moreover $A_h\ge\tfrac34$, and that $P$ has strong credit at $h$ ($\tfrac12\le B_h-1$ or $1-A_h\le(B_h-1)(1-(B_h-1))$). Let $0<q\le1$ and assume $\mathrm{env}_{h,q}(t)\ge0$ for every active $t>h$. Then at least one of the following holds:
--
--   1. a checkpoint certificate for $P$ exists (a point $p$ of support size at most $2$ with $\tfrac34B_t\le P.\mathrm{value}_t(p)$ for all $t$, together with safe entry and exit paths of total length at most $(m+1)+2$ pieces);
--   2. for every active $t>h$,
--   $$\mathrm{act}_{h,q}(t)=4A_h-3-q\,(A_h-A_t)-\Bigl(q-\tfrac{q^2}{4}\Bigr)R(h,t)\;<\;0,$$
--   that is, no later active stage is actually eligible.
--
--   This is the low-parameter case of the test in the checkpoint constructor of Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ConstructorTests.lean#L81-L104 (`ConsistentSubmodular.AtomicProfile.low_actual_test`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.low_actual_test (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hcredit : P.StrongCredit h)
    (access : AccessCertificate P h) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → P.actualEligibility h q t < 0 := by sorry
