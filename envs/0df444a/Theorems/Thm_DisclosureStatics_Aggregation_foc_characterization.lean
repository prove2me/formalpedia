-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_foc_characterization
-- name    : DisclosureStatics.Aggregation.foc_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:32.990619+00:00
-- url     : https://prove2.me/theorems/e36ae4e0-3df7-419f-9345-d3879ff6387a
-- title:
--   Eqs. (1)–(3), pp. 13–16 — the FOCs characterize the solutions of (DP-π), (DP-ρ) and (DP-B)
-- statement:
--   Under the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$:
--
--   1. for every PDS $\pi$ and every bundle $c$, $c$ solves (DP-$\pi$) if and only if $c$ satisfies the budget constraint and there is $\lambda>0$ with
--   $$\varphi'\bigl(V_{S_k}(c)\bigr)\,u'(c_i)=\lambda\,r_i\qquad\text{for all } S_k\in\pi,\ s_i\in S_k; \tag{1}$$
--   applied to the aggregated PDS $\rho$ this is condition (2);
--   2. for every nonempty event $B$ with $s_1\notin B$ and all bundles $c,c^*$, $c^*$ solves (DP-B) given $c$ if and only if $c^*=c$ off $B$, $\sum_{s_i\in B}p_ic^*_i=\sum_{s_i\in B}p_ic_i$, and there is $\lambda>0$ with
--   $$\varphi'\bigl(V_B(c^*)\bigr)\,u'(c^*_i)=\lambda\,r_i\qquad\text{for all } s_i\in B. \tag{3}$$
--
--   Here $r_i=p_i/P(s_i)$. These conditions are the basic tool of every comparative-statics argument of the paper; the multipliers they define are compared in Lemma 3.
--
--   **Formalization Note** The paper writes $\lambda_\pi\ge0$; positivity follows because $\varphi'>0$, $u'>0$ and $r_i>0$, and the formal statement asserts the stronger $\lambda>0$. Since every event of a partition is nonempty, the multiplier is uniquely determined by the bundle.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), pp. 13–14, eqs. (1) and (2); p. 16, eq. (3)

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- The first-order conditions (1)–(3) (pp. 13–16) characterize the solutions of (DP-π),
(DP-ρ) and (DP-B), with a positive multiplier. -/
theorem foc_characterization {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    (∀ π : PDS Ω, IsPDS M π → ∀ c : Ω → ℝ,
      (IsDemand M (cara γ) φ π c ↔
        Budget M c ∧ ∃ lam : ℝ, 0 < lam ∧ IsFOC M (cara γ) φ π c lam)) ∧
    (∀ B : Finset Ω, B.Nonempty → M.s₁ ∉ B → ∀ c cs : Ω → ℝ,
      (IsIntermediate M (cara γ) φ B c cs ↔
        (∀ i ∉ B, cs i = c i) ∧ ∑ i ∈ B, M.p i * cs i = ∑ i ∈ B, M.p i * c i ∧
          ∃ lam : ℝ, 0 < lam ∧ IsFOCB M (cara γ) φ B cs lam)) := by sorry
end DisclosureStatics.Aggregation
