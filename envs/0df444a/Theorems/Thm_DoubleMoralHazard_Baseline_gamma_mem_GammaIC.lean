-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_gamma_mem_GammaIC
-- name    : DoubleMoralHazard.Baseline.gamma_mem_GammaIC
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T21:43:26.507442+00:00
-- url     : https://prove2.me/theorems/4f3e48ea-d9a9-4a9f-b87c-bd53ceabaea6
-- title:
--   Theorem 1, p. 21 (membership) — γⁱ(w) ∈ Γ^IC for every w ∈ [0, w̄ⁱ] in scenario i
-- statement:
--   Fix a scenario $i\in\{1,2,3\}$: $c\le\mu pR^u$, or $\mu pR^u<c<\mu R^u$, or $c\ge\mu R^u$. For every initial promised utility $w\in[0,\bar w^i]$, the tenure-and-termination contract $\gamma^i(w)$ of Definition $i$ (pp. 15–17) belongs to the space of incentive compatible contracts:
--   $$\gamma^i(w)\in\Gamma^{IC}.$$
--
--   Concretely, $\gamma^i(w)$ is a measurable contract with limited liability (payments are made only at observed arrivals and are nonnegative); under it, full effort with truthful reporting $(\bar\nu,N^u)$ gives the agent at least as much utility $u(\gamma^i(w),\nu,\hat N^u)$ as any other measurable effort-and-reporting strategy; and the agent's expected discounted payments under $(\bar\nu,N^u)$ are finite.
--
--   The reason is the construction of the contracts: the promised-utility jumps are $(H^u,H^o)=(R^u,0)$ in Scenario 1, $(R^u,\beta^o)$ in Scenario 2 and $(\beta,\beta)$ in Scenario 3, each capped at the tenure threshold with the excess paid out, so in each scenario's parameter range they satisfy (IC-truthful) $H^u\ge R^u$ and (IC-effort) $pH^u+(1-p)H^o\ge\beta$.
--
--   This is the membership half of Theorem 1 (the optimal contract $\gamma^i(w^i)$ lies in $\Gamma^{IC}$), stated for every $w\in[0,\bar w^i]$; the maximizer $w^i$ of $F_i$ always lies in this interval because $F_i$ has slope $-1$ beyond $\bar w^i$.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint), p. 21, Theorem 1 (the assertion that γⁱ(wⁱ) is a contract in Γ^IC), with Definitions 1–3, pp. 15–17 (jumps satisfying (IC-truthful) and (IC-effort))

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts
import Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts

namespace DoubleMoralHazard.Baseline

open Set

/-- Theorem 1, p. 21 (membership half): in scenario `i`, for every promised utility
`w ∈ [0, w̄ⁱ]` the tenure-and-termination contract `γⁱ(w)` of Definitions 1–3 lies in `Γ^IC`: it is a
measurable contract with limited liability, it satisfies (IC) against every measurable effort and
reporting strategy, and its expected payments under full effort and truthful reporting are finite. -/
theorem gamma_mem_GammaIC (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ w ∈ Icc 0 P.wbar1, gamma1 P w ∈ GammaIC P) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ w ∈ Icc 0 P.wbar2, gamma2 P w ∈ GammaIC P) ∧
    (P.mu * P.Ru ≤ P.c → ∀ w ∈ Icc 0 P.wbar3, gamma3 P w ∈ GammaIC P) := by sorry

end DoubleMoralHazard.Baseline
