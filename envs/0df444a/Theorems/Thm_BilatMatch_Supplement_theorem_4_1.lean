-- Prove2me | Theorems.Thm_BilatMatch_Supplement_theorem_4_1
-- name    : BilatMatch.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:30:12.775832+00:00
-- url     : https://prove2.me/theorems/c0a4b4a9-f189-43bb-b499-71a50f641287
-- title:
--   Theorem 4.1 (Sharp MHR Bounds) — worst-case $V_\alpha/\mathrm{FB}=\beta_\alpha$ and $\mathrm{SB}/\mathrm{FB}=\gamma_{\mathrm{MHR}}\approx0.72490721$ for MHR buyers
-- statement:
--   Let $M_t(\xi)=t\int_0^1\lambda^{t-1}e^{\xi\lambda}d\lambda$, let $\xi_t$ be the root in $(1-t,2(1-t))$ of $(\xi+2t-1)M_t(\xi)=te^{\xi}$, set $\beta_0=1$, $\beta_\alpha=M_t(\xi_t)^{-1}$ with $t=(1+\alpha)^{-1}$ for $\alpha>0$, and $\gamma_{\mathrm{MHR}}=\min_{0<t<1}1/M_t(\xi_t)$. Consider matching markets with countably many agents, downward-closed feasibility, independent priors, $\mathrm{FB}<\infty$, MHR buyers and arbitrary sellers. Then:
--
--   1. for every $t\in(0,1)$ the balance equation has exactly one root in $(1-t,2(1-t))$;
--   2. the minimum defining $\gamma_{\mathrm{MHR}}$ is attained, and $|\gamma_{\mathrm{MHR}}-0.72490721|\le5\cdot10^{-9}$;
--   3. for every $\alpha\ge0$ and every such market,
--   $$V_\alpha\ \ge\ \beta_\alpha\,\mathrm{FB};$$
--   4. for every $\alpha\ge0$ and $\varepsilon>0$ there is a bilateral trade whose buyer is MHR and has a density, with $0<\mathrm{FB}<\infty$ and $V_\alpha\le(\beta_\alpha+\varepsilon)\mathrm{FB}$;
--   5. for every such market,
--   $$\mathrm{SB}\ \ge\ \gamma_{\mathrm{MHR}}\,\mathrm{FB}\qquad\text{and}\qquad \mathrm{SB}_{\mathrm{sbb}}\ \ge\ \gamma_{\mathrm{MHR}}\,\mathrm{FB},$$
--   where $\mathrm{SB}_{\mathrm{sbb}}$ is the second best over mechanisms with ex-post strong budget balance;
--   6. for every $\varepsilon>0$ there is a bilateral trade whose buyer is MHR and has a density, with $0<\mathrm{FB}<\infty$ and $\mathrm{SB}\le(\gamma_{\mathrm{MHR}}+\varepsilon)\mathrm{FB}$.
--
--   Thus the worst-case ratio $V_\alpha/\mathrm{FB}$ over $\mathrm{FB}>0$ is $\beta_\alpha$ and $\inf_{\mathrm{FB}>0}\mathrm{SB}/\mathrm{FB}=\gamma_{\mathrm{MHR}}$, both in bilateral trade and in matching markets, also when buyers must have densities; the second-best guarantee survives ex-post strong budget balance.
--
--   **Formalization Note** $V_\alpha$ and $\mathrm{SB}$ are the whole-line benchmarks of the mission; "has a density" is absolute continuity with respect to Lebesgue measure; MHR allows an atom at the top of the support and unbounded supports.
--
--   Differences from the source:
--   - encoding: the worst-case ratio inf_{FB>0} V_α/FB over bilateral trade (and over matching markets) with an MHR buyer is β_α → V_α ≥ β_α FB on every admitted market (bilateral included), and for every ε > 0 a bilateral trade with an MHR buyer and 0 < FB < ∞ with V_α ≤ (β_α + ε) FB; reason: a bilateral trade is a one-edge matching market, so the lower bound plus near-tight bilateral examples is equivalent to both infima; FB = 0 markets satisfy the lower bound trivially
--   - encoding: inf_{FB>0} SB/FB = γ_MHR in both settings → SB ≥ γ_MHR FB on every admitted market, and for every ε > 0 a bilateral trade with an MHR buyer and 0 < FB < ∞ with SB ≤ (γ_MHR + ε) FB; reason: same equivalence as for V_α
--   - encoding: ξ_t is the unique root in (1 − t, 2(1 − t)); γ_MHR := min_{0<t<1} 1/M_t(ξ_t) → existence and uniqueness of the root and attainment of the minimum (IsLeast) are conjuncts; ξ_t is chosen by Classical.epsilon and γ_MHR is the real sInf; reason: the paper asserts both in the definitions; stating them makes the defined values the paper's
--   - encoding: γ_MHR ≃ 0.72490721 → |γ_MHR − 0.72490721| ≤ 5·10⁻⁹; reason: the value is printed to eight decimals
--   - reading: The same worst-case factors hold when buyer distributions are required to have densities (the sentence following the theorem, p.17) → the near-tight bilateral examples of both ratios have a buyer with GB ≪ Lebesgue; reason: this claim follows the theorem on the same page and is proved with it (Lemma 4.4, §4.3); the lower bounds hold for all MHR buyers, density buyers included
--   - encoding: MHR buyer (p.17): density below the upper endpoint, nondecreasing hazard rate, atom at the upper endpoint allowed → IsMHR: a probability measure with density f (on ℝ, or below some u with an atom μ{u} at u) and f(v)/μ((v,∞)) nondecreasing where the survival is positive, for some version f; reason: the paper's definition; deterministic priors are included, as used on p.41
--   - encoding: ex-post strong budget balance → HasSum (fun u => pay θ u) 0 at every report profile θ, in SBsbb; reason: the payments sum to zero at every profile; for finitely many agents this is ∑_u p_u(θ) = 0
--   - encoding: sellers unrestricted; matching markets with MHR buyers (countable, FB < ∞) → any valid countable Market with every buyer IsMHR and FB < ∞; sellers any Borel probability measures; reason: §4.3 extends the bounds to general priors and countable markets; FB < ∞ is the standing assumption of p.6
--   - encoding: V_α and FB of a market with general priors → whole-line Valpha (EReal supremum over admissible BIC/IIR mechanisms) and FB as a lintegral, with FB < ∞ as a hypothesis; reason: the published base conventions; p.7 defines V_α for general priors as this supremum and p.6 assumes FB < ∞
--   - encoding: α ≥ 0 with t = (1 + α)^{−1}, β_0 = 1 → betaAlpha α = 1 at α = 0 and (M_t(ξ_t))⁻¹ with t = (1 + α)⁻¹ for α > 0; reason: the paper's definition
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem 4.1 with the definitions of M_t, ξ_t, β_α and eqs. (10)–(11), and the sentence following it, p.17 (pdf p.19); MHR definition p.17; proof §4.1–4.3, pp.17–23

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB
import Definitions.Def_BilatMatch_bilateral
import Definitions.Def_BilatMatch_Supplement_IsMHR
import Definitions.Def_BilatMatch_Supplement_betaAlpha
import Definitions.Def_BilatMatch_Supplement_SBsbb

open MeasureTheory

universe u

namespace BilatMatch.Supplement

open BilatMatch

/-- **Theorem 4.1 (Sharp MHR Bounds).** Liu, Qin, Wang, *From Bilateral Trade to Matching Markets:
Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256 ff1490ad…), Theorem 4.1 with the
definitions of `M_t`, `ξ_t`, `β_α` and eqs. (10)–(11), p.17 (pdf p.19); MHR as defined on p.17.

The conjunction states, in order:
1. for every `t ∈ (0, 1)` the balance equation (10) has exactly one root in `(1 − t, 2(1 − t))`;
2. the infimum `γ_MHR` of `1/M_t(ξ_t)` over `t ∈ (0, 1)` is attained (a minimum), and
3. `|γ_MHR − 0.72490721| ≤ 5·10⁻⁹` (the printed eight decimals);
4. for every `α ≥ 0`: `V_α ≥ β_α FB` on every matching market (bilateral trade included) with
   countably many agents, MHR buyers, arbitrary sellers, downward-closed feasibility and `FB < ∞`;
5. for every `α ≥ 0` and `ε > 0` there is a bilateral trade with an MHR buyer that has a density and
   `0 < FB < ∞` with `V_α ≤ (β_α + ε) FB` (so the worst-case ratio over `FB > 0` is `β_α`, in bilateral
   trade and in matching markets, also when buyers must have densities);
6. on every market of item 4, `SB ≥ γ_MHR FB` and also `SB_sbb ≥ γ_MHR FB` (ex-post strong budget
   balance, a supremum over feasible mechanisms);
7. for every `ε > 0` there is a bilateral trade with an MHR buyer that has a density and
   `0 < FB < ∞` with `SB ≤ (γ_MHR + ε) FB` (so `inf_{FB>0} SB/FB = γ_MHR` in both settings, also with
   density buyers).

**Formalization Note**
* `V_α`, `SB` are the published whole-line `Valpha`, `SB`; `FB` is a `lintegral` and `β FB` means
  `β * (FB I).toReal`; `FB < ∞` is the paper's standing assumption (p.6).
* Sellers are arbitrary Borel probability measures (validity of the market); buyers satisfy `IsMHR`
  (density below the top of the support, nondecreasing hazard rate, a possible atom at the top,
  any support). "Has a density" is absolute continuity with respect to Lebesgue measure.
* The worst-case-ratio identities are stated as a lower bound on every admitted market plus
  near-tight bilateral examples for every `ε > 0`; a bilateral trade is a one-edge matching market,
  so this is equivalent to both infima. -/
theorem theorem_4_1 :
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃! ξ, IsBalanceRoot t ξ) ∧
    IsLeast ((fun t => (Mt t (xi t))⁻¹) '' Set.Ioo 0 1) gammaMHR ∧
    |gammaMHR - 0.72490721| ≤ 5e-9 ∧
    (∀ α : ℝ, 0 ≤ α → ∀ {B S : Type u} [Countable B] [Countable S] (I : Market B S),
      I.IsValid → FB I < ⊤ → (∀ i, IsMHR (I.buyerLaw i)) →
        ((betaAlpha α * (FB I).toReal : ℝ) : EReal) ≤ Valpha I α) ∧
    (∀ α : ℝ, 0 ≤ α → ∀ ε : ℝ, 0 < ε → ∃ GB GS : Measure ℝ, IsMHR GB ∧ GB ≪ volume ∧
      IsProbabilityMeasure GS ∧ 0 < FB (bilateral GB GS) ∧ FB (bilateral GB GS) < ⊤ ∧
      Valpha (bilateral GB GS) α ≤ (((betaAlpha α + ε) * (FB (bilateral GB GS)).toReal : ℝ) : EReal)) ∧
    (∀ {B S : Type u} [Countable B] [Countable S] (I : Market B S),
      I.IsValid → FB I < ⊤ → (∀ i, IsMHR (I.buyerLaw i)) →
        ((gammaMHR * (FB I).toReal : ℝ) : EReal) ≤ SB I ∧
        ((gammaMHR * (FB I).toReal : ℝ) : EReal) ≤ SBsbb I) ∧
    (∀ ε : ℝ, 0 < ε → ∃ GB GS : Measure ℝ, IsMHR GB ∧ GB ≪ volume ∧
      IsProbabilityMeasure GS ∧ 0 < FB (bilateral GB GS) ∧ FB (bilateral GB GS) < ⊤ ∧
      SB (bilateral GB GS) ≤ (((gammaMHR + ε) * (FB (bilateral GB GS)).toReal : ℝ) : EReal)) := by sorry

end BilatMatch.Supplement
