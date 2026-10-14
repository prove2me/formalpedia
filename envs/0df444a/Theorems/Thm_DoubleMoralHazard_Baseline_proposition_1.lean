-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_proposition_1
-- name    : DoubleMoralHazard.Baseline.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:22.735982+00:00
-- url     : https://prove2.me/theorems/93c321fe-7aaa-410d-b5fe-96f993fb8871
-- title:
--   Proposition 1, p. 20 — U(γⁱ(w), ν̄, Nᵘ) = Fᵢ(w) and u(γⁱ(w), ν̄, Nᵘ) = w for w ∈ [0, w̄ⁱ]
-- statement:
--   Fix a scenario $i\in\{1,2,3\}$ ($c\le\mu pR^u$; $\mu pR^u<c<\mu R^u$; $c\ge\mu R^u$) and let $F_i$ be a solution of the scenario's value-function equation ((2.9), the corrected (2.11), or (2.13), with $F_i(0)=0$). Then for every promised utility $w\in[0,\bar w^i]$,
--   $$U(\gamma^i(w),\bar\nu,N^u)=F_i(w)\qquad\text{and}\qquad u(\gamma^i(w),\bar\nu,N^u)=w .$$
--   That is, when the agent's total discounted utility under $\gamma^i(w)$ equals $w$, the principal's total discounted utility under $\gamma^i(w)$ is $F_i(w)$.
--
--   Together with Proposition 2 this identifies $F_i$ as the frontier of the principal's utility over incentive compatible contracts that deliver utility $w$ to the agent, attained by $\gamma^i(w)$.
--
--   **Formalization Note** The second equality, $u(\gamma^i(w),\bar\nu,N^u)=w$, is the paper's "That is" sentence made explicit (the starting value $W_{0-}=w$ of the promise-keeping dynamics is the agent's utility); it is needed to combine Propositions 1 and 2. The agent's utility is an extended nonnegative real, hence the cast of $w$. Each conjunct carries its scenario condition, under which Lemma 4 makes $F_i$ unique on $[0,\infty)$.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 20, Proposition 1; proof Appendix B.5, p. 49

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts
import Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts

namespace DoubleMoralHazard.Baseline

open Set

/-- Proposition 1, p. 20: in scenario `i`, for every promised utility `w ∈ [0, w̄ⁱ]` the principal's
utility under the contract `γⁱ(w)` (with full effort and truthful reporting) equals `Fᵢ(w)`, and the
agent's utility under `γⁱ(w)` is `w`. -/
theorem proposition_1 (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F → ∀ w ∈ Icc 0 P.wbar1,
      U P (gamma1 P w) = F w ∧ u P (gamma1 P w) sbar = ENNReal.ofReal w) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ∀ w ∈ Icc 0 P.wbar2,
      U P (gamma2 P w) = F w ∧ u P (gamma2 P w) sbar = ENNReal.ofReal w) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F → ∀ w ∈ Icc 0 P.wbar3,
      U P (gamma3 P w) = F w ∧ u P (gamma3 P w) sbar = ENNReal.ofReal w) := by sorry

end DoubleMoralHazard.Baseline
