-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_3
-- name    : ComplementarySourcing.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:48:14.836014+00:00
-- url     : https://prove2.me/theorems/3725c553-dc99-434e-9d99-145368bb157b
-- title:
--   Theorem 3 — with a fixed wholesale price and Bernoulli risk on $\{0,\epsilon_1\}$, the first-mover disadvantage is reversed or preserved in four explicit regimes
-- statement:
--   Let the wholesale price $w\in[0,r]$ be **fixed**, and let the market taste $\epsilon$ be Bernoulli on $\{0,\epsilon_1\}$ with $\Pr(\epsilon=\epsilon_1)=p_1\in(0,1]$ and $\epsilon_1>0$. The second mover observes the realized $\epsilon$ before investing. Let $\mu>0$ and $\alpha\ge0$. "Reversed" means $\pi_m^M>\pi_m^S$ and $\pi_s^S>\pi_s^M$; "preserved" means $\pi_m^M\le\pi_m^S$ and $\pi_s^S\le\pi_s^M$. For every equilibrium of Model (M) and of Model (S):
--
--   1. If $\epsilon_1\le r\mu/2$ and $\epsilon_1/\mu\le w\le r-\epsilon_1/\mu$, the first-mover disadvantage is reversed.
--   2. Suppose $\epsilon_1>r\mu/2$ and $w=r/2$.
--      1. If $\alpha r\mu\sqrt{p_1}\ge2$, it is reversed.
--      2. If $\sqrt2\le\alpha r\mu\sqrt{p_1}<2$ and
--      $$\epsilon_1<\frac{r\mu\,(2+2\sqrt{p_1}-\alpha r\mu p_1)}{(2-\alpha r\mu\sqrt{p_1})^2},$$
--      it is reversed.
--      3. If $\sqrt2\le\alpha r\mu\sqrt{p_1}<2$ and $\epsilon_1$ is at least that threshold, it is preserved.
--
--   Even without pricing power, leading the investment pays when the margins are balanced or complementarity is strong.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - reading: sample space {0, ϵ1 = 2ϵ0} → 0 < ε₁; reason: the support has two points and ϵ0 > 0 is a mean market taste; at ϵ1 = 0 every profit is 0 and the strict reversals fail
--   - reading: success probability p1 → 0 < p₁ ∧ p₁ ≤ 1; reason: a probability; at p1 = 0 the law is the point 0, every profit is 0, and part 1 fails
--   - reading: "the first-mover disadvantage is reversed" / "preserved" → π^M_m > π^S_m ∧ π^S_s > π^M_s / π^M_m ≤ π^S_m ∧ π^S_s ≤ π^M_s; reason: the proofs compare both firms ("similar proof holds for the supplier", p.A11); Theorems 2, A2, A3 state reversal for both firms; preservation is the failure of the strict comparison, as in Lemma 1's ≤
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - encoding: Bernoulli law on {0, ϵ1} with Prob(ϵ = ϵ1) = p1 → the law ![ε₁, 0] with probabilities ![p₁, 1 − p₁]; reason: the same two-point law
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem 3, p.18; proof pp.A11–A12

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_FixedPriceM_game
import Definitions.Def_ComplementarySourcing_Supplement_FixedPriceS_game
import Definitions.Def_ComplementarySourcing_Supplement_expectedSupplierProfit
import Definitions.Def_ComplementarySourcing_Supplement_expectedManufacturerProfit

namespace ComplementarySourcing.Supplement

/-- **Theorem 3** (First Mover Disadvantage: Fixed Wholesale Price). Let `ϵ` be Bernoulli on
`{0, ϵ₁}` with `Prob(ϵ = ϵ₁) = p₁`, and let the wholesale price `w ∈ [0, r]` be fixed.
1. If `ϵ₁ ≤ rµ/2` and `ϵ₁/µ ≤ w ≤ r − ϵ₁/µ`, the first-mover disadvantage is reversed.
2. Suppose `ϵ₁ > rµ/2` and `w = r/2`.
   (a) If `αrµ√p₁ ≥ 2`, it is reversed.
   (b) If `√2 ≤ αrµ√p₁ < 2` and `ϵ₁ < rµ(2 + 2√p₁ − αrµp₁)/(2 − αrµ√p₁)²`, it is reversed.
   (c) If `√2 ≤ αrµ√p₁ < 2` and `ϵ₁ ≥ rµ(2 + 2√p₁ − αrµp₁)/(2 − αrµ√p₁)²`, it is preserved.
"Reversed" is `π^M_m > π^S_m ∧ π^S_s > π^M_s`, "preserved" `π^M_m ≤ π^S_m ∧ π^S_s ≤ π^M_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem 3, p.18 (PDF 18); proof pp.A11–A12 (PDF 39–40).

**Formalization Note.** The law is `ϵ = ![ϵ₁, 0]` with `p = ![p₁, 1 − p₁]`; the conclusion holds for
every equilibrium `(sM, xM)` of Model (M) and `(sS, xS)` of Model (S). `0 < ϵ₁` (the support
`{0, ϵ₁ = 2ϵ₀}` has two points, `ϵ₀ > 0`) and `0 < p₁ ≤ 1` are readings of the setting: at
`ϵ₁ = 0` or `p₁ = 0` every profit is `0` and part 1's strict reversal fails. -/
theorem theorem_3 {μ α r w ε₁ p₁ xM xS : ℝ} {sM sS : ℝ → Fin 2 → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₁ : 0 < ε₁) (hp₁ : 0 < p₁) (hp₁' : p₁ ≤ 1)
    (hw₀ : 0 ≤ w) (hwr : w ≤ r)
    (hM : (Supplement.FixedPriceM.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).IsEquilibrium sM xM)
    (hS : (Supplement.FixedPriceS.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).IsEquilibrium sS xS) :
    (ε₁ ≤ r * μ / 2 → ε₁ / μ ≤ w → w ≤ r - ε₁ / μ →
      (Supplement.FixedPriceM.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xM (sM xM) >
          Supplement.expectedManufacturerProfit μ α r xS w ![ε₁, 0] ![p₁, 1 - p₁] (sS xS) ∧
        (Supplement.FixedPriceS.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xS (sS xS) >
          Supplement.expectedSupplierProfit μ α xM w ![ε₁, 0] ![p₁, 1 - p₁] (sM xM)) ∧
    (r * μ / 2 < ε₁ → w = r / 2 →
      (2 ≤ α * r * μ * Real.sqrt p₁ →
        (Supplement.FixedPriceM.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xM (sM xM) >
            Supplement.expectedManufacturerProfit μ α r xS w ![ε₁, 0] ![p₁, 1 - p₁] (sS xS) ∧
          (Supplement.FixedPriceS.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xS (sS xS) >
            Supplement.expectedSupplierProfit μ α xM w ![ε₁, 0] ![p₁, 1 - p₁] (sM xM)) ∧
      (Real.sqrt 2 ≤ α * r * μ * Real.sqrt p₁ → α * r * μ * Real.sqrt p₁ < 2 →
        ε₁ < r * μ * (2 + 2 * Real.sqrt p₁ - α * r * μ * p₁) /
            (2 - α * r * μ * Real.sqrt p₁) ^ 2 →
        (Supplement.FixedPriceM.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xM (sM xM) >
            Supplement.expectedManufacturerProfit μ α r xS w ![ε₁, 0] ![p₁, 1 - p₁] (sS xS) ∧
          (Supplement.FixedPriceS.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xS (sS xS) >
            Supplement.expectedSupplierProfit μ α xM w ![ε₁, 0] ![p₁, 1 - p₁] (sM xM)) ∧
      (Real.sqrt 2 ≤ α * r * μ * Real.sqrt p₁ → α * r * μ * Real.sqrt p₁ < 2 →
        r * μ * (2 + 2 * Real.sqrt p₁ - α * r * μ * p₁) /
            (2 - α * r * μ * Real.sqrt p₁) ^ 2 ≤ ε₁ →
        (Supplement.FixedPriceM.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xM (sM xM) ≤
            Supplement.expectedManufacturerProfit μ α r xS w ![ε₁, 0] ![p₁, 1 - p₁] (sS xS) ∧
          (Supplement.FixedPriceS.game μ α r w ![ε₁, 0] ![p₁, 1 - p₁]).leaderPayoff xS (sS xS) ≤
            Supplement.expectedSupplierProfit μ α xM w ![ε₁, 0] ![p₁, 1 - p₁] (sM xM))) := by sorry

end ComplementarySourcing.Supplement
