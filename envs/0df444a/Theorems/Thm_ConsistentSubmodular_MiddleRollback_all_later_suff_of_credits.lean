-- Prove2me | Theorems.Thm_ConsistentSubmodular_MiddleRollback_all_later_suff_of_credits
-- name    : ConsistentSubmodular.MiddleRollback.all_later_suff_of_credits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:59.110699+00:00
-- url     : https://prove2.me/theorems/229c9d70-de73-48ef-ad9d-fff2f7aaf544
-- title:
--   Middle rollback — every later row is covered by the sufficient test
-- statement:
--   Let $P$ be a canonical atomic profile on stages $0,\dots,m$. For a stage $t$ write $A_t$ for its designated mass, $B_t$ for its baseline, $r_{i,t}$ for the residual of label $i$ at stage $t$, and $P_t=B_t+A_t$ for the benchmark. Put
--
--   - deficit $d_t=1-A_t$, shifted benchmark $\hat P_t=P_t-1$, gap $g_{a,t}=A_t-r_{a,t}$;
--   - stage $t$ is *active* if $B_t<3A_t$; it is *parent-eligible* for $(a,k)$ if $(k-1)d_t+(4-k)d_a\le g_{a,t}$;
--   - $c(k,d_0)=2-\frac3k+\frac{3(4-k)d_0}{k}$, $\;U(k,d_0,d,p,W)=d-2c(k,d_0)+3p-(3-k)W$, $\;V(k,d_0,d,p,\delta)=p+(3-2k)(d+\delta)-2(4-k)d_0$;
--   - the sufficient row $\mathrm{suff}_{a,h,t}(k)=B_t+\bigl(1-\tfrac k4\bigr)r_{a,t}+\tfrac k4\,r_{h,t}-\tfrac14\min(r_{a,t},r_{h,t})$.
--
--   Let $a\ne h$ and $s$ be stages with $h\le s$, and let $\tfrac32\le k\le 2$. Assume
--
--   1. (credit) for every $t\ge h$ that is active and parent-eligible for $(a,k)$: $\hat P_t\le c(k,d_a)$;
--   2. $0\le U(k,d_a,d_h,\hat P_h,g_{a,h})$;
--   3. $0\le V(k,d_a,d_h,\hat P_h,d_s-d_h)$;
--   4. $0\le \hat P_s-(k-1)+(k-2)^2d_s-(4-k)^2d_a$.
--
--   Then for every stage $t\ge h$,
--   $$\tfrac34\,P_t\le \mathrm{suff}_{a,h,t}(k).$$
--
--   The three scalar conditions $U,V,Z\ge0$ partition all later rows, so that the mixture of the parent $a$ and the rollback stage $h$ satisfies the $\tfrac34$ persistence requirement at every stage from $h$ on. This supports the middle rollback step of the deterministic $3/4$ certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleRows.lean#L23-L78 (`ConsistentSubmodular.MiddleRollback.all_later_suff_of_credits`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

open ConsistentSubmodular
open LowRollback
variable {m atomCount : ℕ}

theorem ConsistentSubmodular.MiddleRollback.all_later_suff_of_credits (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (a h s : Fin (m + 1)) (hah : a ≠ h) (_hhs : h ≤ s)
    (k : ℝ) (hk : 3 / 2 ≤ k) (hk2 : k ≤ 2)
    (hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k (deficit P a))
    (hU : 0 ≤ U k (deficit P a) (deficit P h) (shifted P h) (gap P a h))
    (hV : 0 ≤ V k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hZ : 0 ≤ shifted P s - (k - 1) + (k - 2) ^ 2 * deficit P s - (4 - k) ^ 2 * deficit P a) :
    ∀ t, h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤ suffRow P a h t k := by sorry
