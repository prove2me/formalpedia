-- Prove2me | Theorems.Thm_AuditEvasion_eq_12_unique_root
-- name    : AuditEvasion.eq_12_unique_root
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:44.575674+00:00
-- url     : https://prove2.me/theorems/d0d00a0b-4b8e-40b0-97a7-7322ede62c70
-- title:
--   Eq. (12), p.1850 — $\Gamma(t;h)=0$ has a unique positive root $t^\star$
-- statement:
--   Let $\lambda,\theta,k,h>0$ and $h\le F$. Then the equation
--
--   $$\Gamma(t;h)=(\lambda+\theta)\big[F-(k+F)e^{-\lambda t}\big]-\lambda h\big[1-e^{-(\lambda+\theta)t}\big]=0\qquad(12)$$
--
--   has exactly one solution $t^\star>0$.
--
--   This root fixes the length of the audit-free period of each cycle of the optimal policy (Theorem 2).
--
--   Differences from the source:
--   - reading: t⋆ 'the unique solution' of (12) → the unique positive solution of (12); reason: Γ(0) = −(λ+θ)k < 0 and Γ(t) → +∞ as t → −∞, so (12) also has a negative root; Theorem 3 (p.1852) calls the root of the same equation the 'unique positive solution'
--   - generalization: (12) under the standing assumptions of §3 and β = 0 → only λ, θ, k, h > 0 and h ≤ F; reason: (12) involves only these parameters; the claim specializes to the paper's setting
--   - reading: audit cost k (sign not stated, p.1847) → 0 < k; reason: Corollary 1 asserts A⋆ > 0, which needs k > 0
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, Theorem 2, eq. (12), p.1850 (PDF 9)

import Mathlib
import Definitions.Def_AuditEvasion_Model
import Definitions.Def_AuditEvasion_Gamma

namespace AuditEvasion

/-- Equation (12), Oper. Res. 72(5) (2024), Theorem 2, p.1850: for `λ, θ, k, h > 0` and `h ≤ F`,
the equation `Γ(t; h) = 0` has exactly one positive solution `t⋆`.

**Formalization Note** (12) also has a negative root (`Γ(0) = −(λ+θ)k < 0` and `Γ(t) → +∞` as
`t → −∞`); "the unique solution" is read as the unique positive one, as Theorem 3 (p.1852) says
of the same equation. -/
theorem eq_12_unique_root (p : Params) (hlam : 0 < p.lam) (htheta : 0 < p.theta)
    (hk : 0 < p.k) (hh : 0 < p.h) (hhF : p.h ≤ p.F) :
    ∃! t : ℝ, 0 < t ∧ Gamma p t = 0 := by sorry

end AuditEvasion
