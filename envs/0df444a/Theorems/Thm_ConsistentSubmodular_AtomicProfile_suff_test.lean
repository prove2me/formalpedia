-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_suff_test
-- name    : ConsistentSubmodular.AtomicProfile.suff_test
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:15.953653+00:00
-- url     : https://prove2.me/theorems/08cac981-fb4f-4268-a395-46b0956c4628
-- title:
--   Sufficient-eligibility test for the checkpoint constructor
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ (designated values $A_t$, residuals $R(i,t)$, benchmarks $B_t$), let $h$ be a stage, and let an access certificate for $(P,h)$ be given: a polygonal path from vertex $0$ to vertex $h$ with at most $h$ pieces, safe at level $\tfrac34$ for the stage-$0$ value of $P$. Call a stage $t$ active if its baseline is below $3A_t$, and let the envelope slack be
--   $$\mathrm{env}_{h,q}(t)=q\bigl[(A_h-A_t)+(A_t-R(h,t))\bigr]+(B_t-A_h)+3(1-A_h)-4\,(A_t-R(h,t)).$$
--
--   Let $q\in[\tfrac32,3]$ and assume $\mathrm{env}_{h,q}(t)\ge0$ for every active $t>h$. Then at least one of the following holds:
--
--   1. a checkpoint certificate for $P$ exists (a point $p$ of support size at most $2$ with $\tfrac34B_t\le P.\mathrm{value}_t(p)$ for all $t$, together with safe entry and exit paths of total length at most $(m+1)+2$ pieces);
--   2. for every active $t>h$ with sufficient eligibility $\mathrm{suff}_{h,q}(t)\ge 0$, where
--   $$\mathrm{suff}_{h,q}(t)=(A_t-R(h,t))-(q-1)(A_h-A_t)-3(1-A_h),$$
--   one has
--   $$q\,(B_t-A_h)\;<\;2A_h\,q-3\,(4A_h-3).$$
--
--   This is the large-parameter counterpart of the actual-eligibility test in the constructor of Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ConstructorTests.lean#L50-L79 (`ConsistentSubmodular.AtomicProfile.suff_test`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.suff_test (hP : P.Canonical) (h : Fin (m + 1))
    (access : AccessCertificate P h) (q : ℝ) (hq : (3 : ℝ) / 2 ≤ q) (hq3 : q ≤ 3)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → 0 ≤ P.suffEligibility h q t →
        q * (P.benchmark t - P.designated h) <
          2 * P.designated h * q - 3 * (4 * P.designated h - 3) := by sorry
