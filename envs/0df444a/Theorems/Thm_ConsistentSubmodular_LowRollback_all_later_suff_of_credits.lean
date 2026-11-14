-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_all_later_suff_of_credits
-- name    : ConsistentSubmodular.LowRollback.all_later_suff_of_credits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:25.009901+00:00
-- url     : https://prove2.me/theorems/6ad92c9c-e9db-4b9e-8e84-7e9bddc017f9
-- title:
--   Sufficient rows from credits in low rollback
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ (baseline $L_t$, designated values $A_t$, residuals $R(i,t)$, benchmarks $B_t$). Write $\mathrm{def}_t=1-A_t$, $\sigma_t=B_t-1$, $\mathrm{gap}(a,t)=A_t-R(a,t)$, and call $t$ active if $L_t<3A_t$. For $k\in\mathbb{R}$ let
--   $$\mathrm{ceil}(k,d_0)=2-\frac3k+\frac{3(4-k)d_0}{k},$$
--   $$\mathrm{row}_{a,h}(t)=L_t+\bigl(1-\tfrac k4\bigr)R(a,t)+\tfrac k4R(h,t)-\tfrac14\min\{R(a,t),R(h,t)\},$$
--   and let $U,V,V_{\rm High},Y$ be the scalar margins $U(k,d_0,d,p,W)=d-2\,\mathrm{ceil}(k,d_0)+3p-(3-k)W$, $V(k,d_0,d,p,\delta)=p+(3-2k)(d+\delta)-2(4-k)d_0$, $V_{\rm High}(k,d_0,d,p,\delta)=p-(k-2)-(k-1)(3-k)(d+\delta)-(4-k)^2d_0$, and $Y$ as in the after-attainer bound. Call $t$ parent-eligible for $(a,k)$ if $(k-1)\,\mathrm{def}_t+(4-k)\,\mathrm{def}_a\le \mathrm{gap}(a,t)$.
--
--   Let $a\ne h$ and $h\le s$ be stages, $\tfrac32<k<3$, with $s$ active and $\mathrm{ceil}(k,\mathrm{def}_a)<\sigma_s$. Assume
--
--   * (credits) for every active $t\ge h$ that is parent-eligible for $(a,k)$: $\sigma_t\le\mathrm{ceil}(k,\mathrm{def}_a)$;
--   * $0\le U(k,\mathrm{def}_a,\mathrm{def}_h,\sigma_h,\mathrm{gap}(a,h))$;
--   * if $k\le2$: $0\le V(k,\mathrm{def}_a,\mathrm{def}_h,\sigma_h,\mathrm{def}_s-\mathrm{def}_h)$;
--   * if $k\ge2$: $0\le V_{\rm High}(k,\mathrm{def}_a,\mathrm{def}_h,\sigma_h,\mathrm{def}_s-\mathrm{def}_h)$;
--   * $0\le Y(k,\mathrm{def}_a,\mathrm{def}_h,\sigma_h,\mathrm{def}_s-\mathrm{def}_h,\sigma_s)$.
--
--   Then for every stage $t\ge h$,
--   $$\tfrac34\,B_t\;\le\;\mathrm{row}_{a,h}(t).$$
--
--   The eligible, before-attainer and after-attainer rows from the attaining parent child onward are all covered (inactive rows via their baseline), so the whole tail satisfies the sufficient-row bound. This is the partition step of the low-rollback argument in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackTargets.lean#L163-L245 (`ConsistentSubmodular.LowRollback.all_later_suff_of_credits`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.all_later_suff_of_credits (P : AtomicProfile m aCount) (hP : P.Canonical)
    (a h s : Fin (m + 1)) (hah : a ≠ h) (hhs : h ≤ s)
    (k : ℝ) (hk : 3 / 2 < k) (hk3 : k < 3)
    (hs : Active P s)
    (hsource : ceiling k (deficit P a) < shifted P s)
    (hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k (deficit P a))
    (hU : 0 ≤ U k (deficit P a) (deficit P h) (shifted P h) (gap P a h))
    (hV : k ≤ 2 → 0 ≤ V k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hVh : 2 ≤ k → 0 ≤ VHigh k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hY : 0 ≤ Y k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h) (shifted P s)) :
    ∀ t : Fin (m + 1), h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤
      suffRow P a h t k := by sorry
