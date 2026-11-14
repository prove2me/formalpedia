-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_before_low_margin
-- name    : ConsistentSubmodular.LowRollback.before_low_margin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:54.223222+00:00
-- url     : https://prove2.me/theorems/88da7a6e-e506-4709-b13b-d976cf925b52
-- title:
--   Before-attainer margin bound for low rollback
-- statement:
--   Let $k,d_0,d,p,\delta,\Delta,P_t,z,u\in\mathbb{R}$ satisfy
--
--   * $\tfrac32\le k\le 2$;
--   * $\Delta\le\delta$;
--   * $0\le P_t-p-u$;
--   * $z\le (k-1)(d+\Delta)+(4-k)\,d_0$.
--
--   Define
--   $$V(k,d_0,d,p,\delta)=p+(3-2k)(d+\delta)-2(4-k)\,d_0,$$
--   $$M_1(k,T,P_t,z,u)=T+P_t-(3-k)z-ku,\qquad M_2(k,T,P_t,z,u)=T+P_t-(4-k)z-(k-1)u .$$
--   Then
--   $$V(k,d_0,d,p,\delta)\;\le\;\max\bigl\{M_1(k,d+\Delta,P_t,z,u),\;M_2(k,d+\Delta,P_t,z,u)\bigr\}.$$
--
--   This scalar estimate controls rows lying before the attainer in the low-rollback argument of the deterministic certificates (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackTargets.lean#L73-L91 (`ConsistentSubmodular.LowRollback.before_low_margin`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.before_low_margin (k d₀ d p δ Δ Pt z u : ℝ)
    (hk : 3 / 2 ≤ k) (hk2 : k ≤ 2) (hΔ : Δ ≤ δ)
    (hp : 0 ≤ Pt - p - u) (hcap : z ≤ (k - 1) * (d + Δ) + (4 - k) * d₀) :
    V k d₀ d p δ ≤ max (M₁ k (d + Δ) Pt z u) (M₂ k (d + Δ) Pt z u) := by sorry
