-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_a3
-- name    : ComplementarySourcing.Supplement.theorem_a3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:51:32.227795+00:00
-- url     : https://prove2.me/theorems/c63e4bb0-7280-44ed-b47c-932994eaad47
-- title:
--   Theorem A3 — with known constant market appetite and a fixed balanced wholesale price, the first-mover disadvantage is reversed for both firms
-- statement:
--   Suppose the market appetite is known and constant, $\epsilon\equiv\epsilon_0$, and the wholesale price $w$ is fixed. Let $\mu>0$, $\alpha\ge0$, and suppose
--
--   $$0<\epsilon_0\le\frac{\mu r}{2}\qquad\text{and}\qquad\frac{\epsilon_0}{\mu}\le w\le r-\frac{\epsilon_0}{\mu}.$$
--
--   Then, for every equilibrium of Model (M) and of Model (S), the first-mover disadvantage is reversed for both the manufacturer and the supplier: $\pi_m^M>\pi_m^S$ and $\pi_s^S>\pi_s^M$.
--
--   Without pricing power, a balanced wholesale price is what makes leading the investment pay.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - encoding: ϵ ≡ ϵ0 → the one-point law ![ε₀] with probability ![1]; reason: the same law
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A4, p.A20; Theorem A3, p.A22

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_FixedPriceM_game
import Definitions.Def_ComplementarySourcing_Supplement_FixedPriceS_game
import Definitions.Def_ComplementarySourcing_Supplement_expectedSupplierProfit
import Definitions.Def_ComplementarySourcing_Supplement_expectedManufacturerProfit

namespace ComplementarySourcing.Supplement

/-- **Theorem A3** (constant market risk, fixed wholesale price). Suppose `ϵ ≡ ϵ₀`,
`0 < ϵ₀ ≤ µr/2` and `ϵ₀/µ ≤ w ≤ r − ϵ₀/µ`. Then the first-mover disadvantage is reversed for both
the manufacturer and the supplier: `π^M_m > π^S_m` and `π^S_s > π^M_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A4, p.A20 (PDF 48), and Theorem A3, p.A22 (PDF 50).

**Formalization Note.** The constant law is the one-point law `ϵ = ![ϵ₀]`, `p = ![1]`. The
conclusion holds for every equilibrium `(sM, xM)` of Model (M) and `(sS, xS)` of Model (S). -/
theorem theorem_a3 {μ α r w ε₀ xM xS : ℝ} {sM sS : ℝ → Fin 1 → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hε₀r : ε₀ ≤ μ * r / 2)
    (hw : ε₀ / μ ≤ w) (hw' : w ≤ r - ε₀ / μ)
    (hM : (Supplement.FixedPriceM.game μ α r w ![ε₀] ![1]).IsEquilibrium sM xM)
    (hS : (Supplement.FixedPriceS.game μ α r w ![ε₀] ![1]).IsEquilibrium sS xS) :
    (Supplement.FixedPriceM.game μ α r w ![ε₀] ![1]).leaderPayoff xM (sM xM) >
        Supplement.expectedManufacturerProfit μ α r xS w ![ε₀] ![1] (sS xS) ∧
      (Supplement.FixedPriceS.game μ α r w ![ε₀] ![1]).leaderPayoff xS (sS xS) >
        Supplement.expectedSupplierProfit μ α xM w ![ε₀] ![1] (sM xM) := by sorry

end ComplementarySourcing.Supplement
