-- Prove2me | Theorems.Thm_CrowdContest_Pooling_proposition_1
-- name    : CrowdContest.Pooling.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:25.869718+00:00
-- url     : https://prove2.me/theorems/62b4f80b-a4de-49af-bc76-dba58f9cfd49
-- title:
--   Proposition 1, p. 17 — combination effect Δξ_n > 0 and pooling effect Δe_n < 0 (with the simplified conditions (a), (b))
-- statement:
--   **Proposition 1 (Expected Best Performance).** Let $n\ge 2$ contestants compete, and let the random factors $\xi^1,\xi^2$ of the two attributes be independent with a common symmetric log-concave density $\psi$; $\xi^\circ=\xi^1+\xi^2$ has density $\psi^\circ$.
--
--   1. **(Combination effect.)** If Assumption (R) holds, the expected best random factor in the separate contest is higher than in the joint contest:
--   $$\Delta^\xi_n=\mathsf E(\xi^1_{(n)})+\mathsf E(\xi^2_{(n)})-\mathsf E\big((\xi^1+\xi^2)_{(n)}\big)>0 .$$
--   2. **(Pooling effect.)** Let $A>0$ be the total prize, $w\in(0,1)$ the weight of the first sub-contest and $C_1,C_2$ cost functions. Let $e_1>0$ and $e_2>0$ be symmetric equilibrium efforts of the sub-contests with prizes $wA$ and $(1-w)A$, and let $(s_1,s_2)$ with $s_1,s_2>0$ be a symmetric equilibrium of the joint contest with prize $A$. If
--   $$h^\circ(\xi^\circ;n)>\max\{w\,h(\xi;n),\ (1-w)\,h(\xi;n)\},$$
--   then the equilibrium effort in the joint contest is higher: $\Delta^e_n=e_1+e_2-(s_1+s_2)<0$. Moreover the condition may be replaced by $h^\circ(\xi^\circ;n)>h(\xi;n)/2$ if (a) $w=1/2$, or (b) $C_1=C_2$ and its derivative is convex.
--
--   The two parts are the countervailing forces of the paper: the separate contest picks the best random realization in each attribute, while the joint contest pools the prize into one competition and induces more effort.
--
--   **Formalization Note** Equilibria are pure symmetric Nash equilibria of the expected winner-take-all payoffs over nonnegative efforts, characterized as global best responses; the first-order conditions (Lemmas 1 and 3) are milestones, not definitions. Part (ii) is claimed for every interior equilibrium of the three games (the paper speaks of "the" equilibrium; Lemma 1 makes an interior one unique); interiority is the paper's footnote 8, and both joint-contest efforts are required positive. Joint strategies are pairs, the aggregate effort being $s_1+s_2$. Assumption (R) is a hypothesis of part (i) only: the paper requires it for $\Delta^\xi_n>0$ (p. 16), its footnote 5 says Proposition 1 holds whenever (R) holds, and its remark that every symmetric log-concave density satisfies (R) is cited from the literature, not proved. "Their derivatives are weakly convex" is convexity of $C_1'$ on $(0,\infty)$. Part (i) is the strict inequality, not the pathwise weak inequality of p. 16.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), Proposition 1, p. 17; proof OA pp. 2–3

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Proposition 1 (Expected Best Performance), p. 17. Let `n ≥ 2` and let the random factors
`ξ¹, ξ²` have the symmetric log-concave density `ψ`; `ξ° = ξ¹ + ξ²` has density `ψ°`.
(i) (Combination effect) under Assumption (R), `Δξ_n = E(ξ¹_(n)) + E(ξ²_(n)) - E(ξ°_(n)) > 0`.
(ii) (Pooling effect) for a total prize `A > 0`, a weight `w ∈ (0,1)` and costs `C₁, C₂`, let
`e₁, e₂ > 0` be symmetric equilibrium efforts of the sub-contests with prizes `wA` and `(1-w)A`,
and `(s₁, s₂)` with `s₁, s₂ > 0` a symmetric equilibrium of the joint contest. If
`h°(ξ°; n) > max {w h(ξ; n), (1-w) h(ξ; n)}` then `Δe_n = e₁ + e₂ - (s₁ + s₂) < 0`; and the
condition may be replaced by `h°(ξ°; n) > h(ξ; n)/2` if (a) `w = 1/2`, or (b) `C₁ = C₂` with
convex derivative. -/
theorem proposition_1 (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    (AssumptionR ψ → 0 < deltaXi ψ n) ∧
    ∀ (A w : ℝ) (C₁ C₂ : ℝ → ℝ) (e₁ e₂ s₁ s₂ : ℝ),
      0 < A → 0 < w → w < 1 → IsCost C₁ → IsCost C₂ →
      IsSymEqSub ψ n (w * A) C₁ e₁ → 0 < e₁ →
      IsSymEqSub ψ n ((1 - w) * A) C₂ e₂ → 0 < e₂ →
      IsSymEqJoint ψ n A C₁ C₂ s₁ s₂ → 0 < s₁ → 0 < s₂ →
      (max (w * hFun ψ n) ((1 - w) * hFun ψ n) < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) ∧
      (w = 1 / 2 → hFun ψ n / 2 < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) ∧
      (C₁ = C₂ → ConvexOn ℝ (Set.Ioi 0) (deriv C₁) → hFun ψ n / 2 < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) := by sorry

end CrowdContest.Pooling
