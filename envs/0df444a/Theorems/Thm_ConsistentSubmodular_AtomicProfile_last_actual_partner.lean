-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_actual_partner
-- name    : ConsistentSubmodular.AtomicProfile.last_actual_partner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:26.830806+00:00
-- url     : https://prove2.me/theorems/74a62706-982c-438d-bcb5-031857cfd3c0
-- title:
--   A last eligible partner exists among later active rows
-- statement:
--   Let $P$ be an atomic profile on stages $0,\dots,m$ with designated values $A_t$ and residuals $r_h(t)$, and call a stage $t$ active when its baseline is below $3A_t$. For a stage $h$, a parameter $q\in\mathbb{R}$ and a stage $c$, the actual eligibility is
--   $$E_{h,q}(c)=4A_h-3-q\,(A_h-A_c)-\Big(q-\frac{q^2}{4}\Big)\,r_h(c).$$
--   Let $s$ be a later active stage of $h$ (that is, $s>h$ and $s$ active) with $E_{h,q}(s)\ge0$. Then there is a stage $c$ such that
--
--   1. $c$ is later active for $h$;
--   2. $s\le c$;
--   3. $E_{h,q}(c)\ge0$;
--   4. every active stage $t>c$ has $E_{h,q}(t)<0$.
--
--   So among the eligible later active rows at or after $s$ there is a last one, which serves as the partner $c$ of $h$ in the certificate constructor.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/BaselineStop.lean#L75-L93 (`ConsistentSubmodular.AtomicProfile.last_actual_partner`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.last_actual_partner (h s : Fin (m + 1)) (q : ℝ)
    (hs : s ∈ P.laterActive h) (he : 0 ≤ P.actualEligibility h q s) :
    ∃ c, c ∈ P.laterActive h ∧ s ≤ c ∧ 0 ≤ P.actualEligibility h q c ∧
      ∀ t, c < t → P.Active t → P.actualEligibility h q t < 0 := by sorry
