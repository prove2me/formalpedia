-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_demand_well_defined
-- name    : DisclosureStatics.Aggregation.demand_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:24.312473+00:00
-- url     : https://prove2.me/theorems/c97e9277-546c-48d8-8edc-aa82144d7c02
-- title:
--   §2.4–2.5, pp. 13–16 — (DP-π) and (DP-B) have unique solutions
-- statement:
--   Let the market satisfy the standing assumptions, let $u(x)=(1-e^{-\gamma x})/\gamma$ with $\gamma>0$ (Assumption 1), and let $\varphi$ satisfy Assumption 2 on $(-\infty,1/\gamma)$: it is $C^3$ there with $\varphi'>0$, $\varphi''<0$ and $A_\varphi=-\varphi''/\varphi'$ non-increasing. Then:
--
--   1. for every PDS $\pi$ (a partition of $\Omega$ with $\{s_1\}$ as a block) the insurance demand problem
--   $$\max_{c\,:\;s+\sum_{i\ge2}(l_i-d_i)p_i=I}\;U(c;\pi)$$
--   has exactly one solution;
--   2. for every nonempty event $B$ with $s_1\notin B$ and every bundle $c$, the intermediate problem (DP-B) — maximize $P(B)\varphi(V_B(c^*))$ over bundles $c^*$ with $c^*=c$ off $B$ and $\sum_{s_i\in B}p_ic^*_i=\sum_{s_i\in B}p_ic_i$ — has exactly one solution.
--
--   The paper speaks of "the solution" of (DP-$\pi$) (p. 13) and of (DP-B) (p. 16) without stating a result; this item makes that presupposition explicit. It guarantees that the other results of the mission, which quantify over solutions, are not vacuous.
--
--   **Formalization Note** This is not a numbered result of the paper. Uniqueness is stated with `∃!` over consumption bundles $c:\Omega\to\mathbb R$; deductibles may be negative (footnote 10), so there is no sign constraint.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 13 (§2.4, "we denote the solution to this problem") and p. 16 (§2.5, (DP-B))

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Well-posedness of (DP-π) (p. 13) and of (DP-B) (p. 16) under Assumptions 1–2. -/
theorem demand_well_defined {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    (∀ π : PDS Ω, IsPDS M π → ∃! c : Ω → ℝ, IsDemand M (cara γ) φ π c) ∧
    (∀ B : Finset Ω, B.Nonempty → M.s₁ ∉ B → ∀ c : Ω → ℝ,
      ∃! cs : Ω → ℝ, IsIntermediate M (cara γ) φ B c cs) := by sorry
end DisclosureStatics.Aggregation
