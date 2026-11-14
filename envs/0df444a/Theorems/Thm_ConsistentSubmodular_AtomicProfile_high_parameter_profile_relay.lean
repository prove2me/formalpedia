-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_parameter_profile_relay
-- name    : ConsistentSubmodular.AtomicProfile.high_parameter_profile_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:33.442207+00:00
-- url     : https://prove2.me/theorems/9d3b8a50-b6f8-411e-987b-86e0e401ba5c
-- title:
--   High-parameter relay step for atomic profiles
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$, with designated values $A_t$ (`designated`), residuals $R(i,t)$, benchmarks $B_t$ (`benchmark`), and raw ratio
--   $$\rho(h,s)=\frac{4\,(A_s-R(h,s))-(B_s-A_h)-3\,(1-A_h)}{A_h-R(h,s)} .$$
--   Let $h<s$ be stages such that
--
--   * $A_h>\tfrac34$ and $P$ has strong credit at $h$: $\tfrac12\le B_h-1$ or $1-A_h\le (B_h-1)\bigl(1-(B_h-1)\bigr)$;
--   * $q\ge\tfrac32$, $A_h-R(h,s)>0$, and $\rho(h,s)=q$;
--   * (failure) $q\,(B_s-A_h)<2A_h\,q-3\,(4A_h-3)$.
--
--   Then all three of the following hold:
--
--   1. for every real $z$: $\;\tfrac34<A_h-(A_h-A_s)\,z-R(h,s)\,z(1-z)$;
--   2. $A_s>\tfrac34$;
--   3. $P$ has strong credit at $s$.
--
--   So the edge from vertex $h$ to vertex $s$ is strictly safe at level $3/4$, and the hypotheses (high designated value and strong credit) are inherited by $s$. This is the profile-level form of the high-parameter relay used to extend access certificates in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Access.lean#L110-L143 (`ConsistentSubmodular.AtomicProfile.high_parameter_profile_relay`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

open ConsistentSubmodular
variable {m atomCount : ℕ}
open ConsistentSubmodular.AtomicProfile
variable (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.high_parameter_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (3 : ℝ) / 4 < P.designated h) (hcredit : P.StrongCredit h)
    (q : ℝ) (hq : (3 : ℝ) / 2 ≤ q)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    (∀ z : ℝ, (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z)) ∧
      (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by sorry
