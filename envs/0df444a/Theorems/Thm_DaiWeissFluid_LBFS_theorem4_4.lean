-- Prove2me | Theorems.Thm_DaiWeissFluid_LBFS_theorem4_4
-- name    : DaiWeissFluid.LBFS.theorem4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:44:15.006289+00:00
-- url     : https://prove2.me/theorems/1f0fdd3b-ab1e-40cc-a891-e1ab21c3a36d
-- title:
--   Theorem 4.4 — LBFS fluid stability in every reentrant line
-- statement:
--   Consider any reentrant line with finitely many stations and classes, positive mean service times $m_k$, and nominal station workloads $\rho_i=\sum_{k\in C_i}m_k<1$ for every station $i$. Give higher priority to later route stages: the Last-Buffer-First-Served (LBFS) ranking is $\pi(k)=K+1-k$. Then its preemptive-resume priority fluid model is stable in the sense of Definition 1.3:
--   $$
--   \exists\delta>0\;\forall (Q,T),\quad \bigl[(Q,T)\text{ solves (1.8)--(1.12), (4.4)}\;\land\;|Q(0)|=1\bigr]\Longrightarrow\forall t\ge\delta,\;Q(t)=0.
--   $$
--   Here $|Q(0)|=\sum_kQ_k(0)$ and the same emptying time works for every fluid solution. The result supplies a policy-independent stability guarantee for the LBFS discipline across every route and station assignment satisfying the load condition.
--
--   **Formalization Note** Classes and stations are 0-based `Fin` indices, so LBFS is `Fin.revPerm`. The priority condition (4.4) is represented by the complementary interval condition `ConstantWhile`; equations are imposed on nonnegative time. Positive $m_k$ makes the service rates $1/m_k$ meaningful. The paper assumes $\rho_i<1$ throughout. The empty-route case is harmless in the theorem: the normalization $|Q(0)|=1$ is impossible when $K=0$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 124, Theorem 4.4; p. 116, (1.7); p. 119, Definition 1.3; p. 123, Definition 4.1

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel

namespace DaiWeissFluid.LBFS

/-- Theorem 4.4: every LBFS priority fluid model under (1.7) is stable. -/
theorem theorem4_4 {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) :
    DaiWeissFluid.ThreeBuffer.FluidStable (L.IsPrioritySolution Fin.revPerm) := by sorry

end DaiWeissFluid.LBFS
