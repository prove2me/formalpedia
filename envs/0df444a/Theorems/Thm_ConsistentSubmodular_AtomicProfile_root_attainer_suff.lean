-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_root_attainer_suff
-- name    : ConsistentSubmodular.AtomicProfile.root_attainer_suff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:45.935449+00:00
-- url     : https://prove2.me/theorems/b384e1e6-16aa-4ae9-9bc7-00a4378fa5bf
-- title:
--   Sufficient eligibility of a root attainer
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$, designated values $A_t$, residuals $R(i,t)$, benchmarks $B_t$, and raw ratio
--   $$\rho(0,s)=\frac{4\,(A_s-R(0,s))-(B_s-A_0)-3\,(1-A_0)}{A_0-R(0,s)} .$$
--   Let $s$ be a stage and $q\in\mathbb{R}$ with $A_s<1$, $A_0-R(0,s)>0$, and $\rho(0,s)=q$. Then the sufficient eligibility at the root is strictly positive:
--   $$0\;<\;\bigl(A_s-R(0,s)\bigr)-(q-1)\,(A_0-A_s)-3\,(1-A_0).$$
--
--   Since $P$ is canonical, $A_0=1$, so the term $3(1-A_0)$ vanishes. The lemma shows that at the root, a stage attaining the raw ratio is eligible for the sufficient test, which is used in the partner-selection argument of Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/PartnerSelection.lean#L43-L72 (`ConsistentSubmodular.AtomicProfile.root_attainer_suff`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.root_attainer_suff (hP : P.Canonical) (s : Fin (m + 1)) (q : ℝ)
    (hs : P.designated s < 1)
    (hd : 0 < P.designated 0 - P.residual 0 s) (heq : P.rawRatio 0 s = q) :
    0 < P.suffEligibility 0 q s := by sorry
