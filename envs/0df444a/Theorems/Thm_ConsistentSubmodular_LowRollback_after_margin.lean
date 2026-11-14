-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_after_margin
-- name    : ConsistentSubmodular.LowRollback.after_margin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:52.603971+00:00
-- url     : https://prove2.me/theorems/22f94f6a-e365-4d1c-bbb3-5bfe5104c552
-- title:
--   After-attainer margin bound for low rollback
-- statement:
--   Let $k,d_0,d,p,\delta,P,T,P_t,z,u,z_s\in\mathbb{R}$ satisfy
--
--   * $\tfrac32<k<3$;
--   * $z_s\le (k-1)(d+\delta)+(4-k)\,d_0$;
--   * $z\le(k-1)T+(4-k)\,d_0$;
--   * $0\le P_t-p-u$ and $0\le 1-T-u$;
--   * (source term) $0\le P_t-P-z+z_s$.
--
--   Define $\mathrm{ceil}(k,d_0)=2-\tfrac3k+\tfrac{3(4-k)d_0}{k}$,
--   $$Y(k,d_0,d,p,\delta,P)=\frac{(k-1)(3-k)}{k}\Bigl(P-(k-1)(d+\delta)-(4-k)d_0\Bigr)+\frac{k^2-3k+3}{k}\,p-\mathrm{ceil}(k,d_0),$$
--   and $M_2(k,T,P_t,z,u)=T+P_t-(4-k)z-(k-1)u$. Then
--   $$Y(k,d_0,d,p,\delta,P)\;\le\;M_2(k,T,P_t,z,u).$$
--
--   This bounds the rows after the attainer in the low-rollback argument (Appendix B). The source term $P_t-P-z+z_s\ge0$ is kept among the hypotheses.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackTargets.lean#L105-L130 (`ConsistentSubmodular.LowRollback.after_margin`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.after_margin (k d₀ d p δ P T Pt z u zs : ℝ)
    (hk : 3 / 2 < k) (hk3 : k < 3)
    (hs : zs ≤ (k - 1) * (d + δ) + (4 - k) * d₀)
    (ht : z ≤ (k - 1) * T + (4 - k) * d₀)
    (hchild : 0 ≤ Pt - p - u) (hres : 0 ≤ 1 - T - u)
    (hparent : 0 ≤ Pt - P - z + zs) :
    Y k d₀ d p δ P ≤ M₂ k T Pt z u := by sorry
