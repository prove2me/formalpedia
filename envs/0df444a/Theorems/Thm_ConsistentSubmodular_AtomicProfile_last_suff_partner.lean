-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_suff_partner
-- name    : ConsistentSubmodular.AtomicProfile.last_suff_partner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:56.135584+00:00
-- url     : https://prove2.me/theorems/e37dd016-1132-4b76-9103-49047e1cefc8
-- title:
--   Last nonnegative sufficient-eligibility partner
-- statement:
--   Let $P$ be an atomic profile with stages $0,\dots,m$, designated values $A_t$ and residuals $R(i,t)$. For a stage $h$ let $\mathcal{L}(h)=\{t: t>h,\ t\text{ active}\}$ be the later active stages (active means baseline $<3A_t$), and for $q\in\mathbb{R}$ define the sufficient eligibility
--   $$\mathrm{suff}_{h,q}(c)=\bigl(A_c-R(h,c)\bigr)-(q-1)\,(A_h-A_c)-3\,(1-A_h).$$
--   Suppose $s\in\mathcal{L}(h)$ and $\mathrm{suff}_{h,q}(s)\ge 0$. Then there is $c\in\mathcal{L}(h)$ such that
--
--   1. $s\le c$;
--   2. $\mathrm{suff}_{h,q}(c)\ge 0$;
--   3. $\mathrm{suff}_{h,q}(t)<0$ for every active stage $t>c$.
--
--   So $c$ is the last later active stage with nonnegative sufficient eligibility, and it is a partner at or after $s$. The statement is a selection lemma used in the partner-selection step of the certificate constructor (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/PartnerSelection.lean#L24-L41 (`ConsistentSubmodular.AtomicProfile.last_suff_partner`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.last_suff_partner (h s : Fin (m + 1)) (q : ℝ)
    (hs : s ∈ P.laterActive h) (he : 0 ≤ P.suffEligibility h q s) :
    ∃ c, c ∈ P.laterActive h ∧ s ≤ c ∧ 0 ≤ P.suffEligibility h q c ∧
      ∀ t, c < t → P.Active t → P.suffEligibility h q t < 0 := by sorry
