-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_step_1_cases
-- name    : CCPCollateral.Incentive.step_1_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:17.756686+00:00
-- url     : https://prove2.me/theorems/8bdde98e-a8a0-407a-b205-bf1bd9e76bf2
-- title:
--   Proof of Proposition 2, Step 1, cases 1–3, p. 45 — unique all-r / all-s equilibria outside [F̂, F̄]; two equilibria inside, all-s better
-- statement:
--   Under the standing assumptions, fix $I\in[0,\hat I(0)]$ and $F\in[0,D-I]$, and write
--   $$\mathrm{gap}=(A_{CCP}-I-F)\,\mathcal P-(D-I-F).$$
--   1. $\mathrm{gap}<X^{N-1}(I,F)$ if and only if $F<\hat F(I)$; in that case the only Nash equilibrium is "all members risk-shift".
--   2. $\mathrm{gap}>X^{0}(I,F)$ if and only if $F>\bar F(I)$; in that case the only Nash equilibrium is "all members hedge".
--   3. $X^{N-1}(I,F)\le\mathrm{gap}\le X^0(I,F)$ if and only if $\hat F(I)\le F\le\bar F(I)$; in that case these are exactly the two Nash equilibria, and every member's payoff is strictly higher when all hedge.
--
--   This case split is the core of the equilibrium part of Proposition 2: the cutoffs $\hat F(I)\le\bar F(I)$ separate a region where only risk-shifting is sustainable, a region where both are, and a region where only hedging is.
--
--   **Formalization Note** The page justifies the payoff ranking in case 3 "per Proposition 1"; the statement asserts the ranking itself, as a strict inequality for every member.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), proof of Proposition 2, Step 1, cases 1–3, p. 45

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- Proof of Proposition 2, Step 1, cases 1–3 (p. 45). With
`gap = (A_CCP − I − F) 𝒫 − (D − I − F)`, for `I ∈ [0, Î(0)]` and `F ∈ [0, D − I]`:
case 1, `gap < X^{N−1}(I, F)` iff `F < F̂(I)`, and then "all not hedging" is the unique Nash
equilibrium; case 2, `gap > X^0(I, F)` iff `F > F̄(I)`, and then "all hedging" is the unique Nash
equilibrium; case 3, `X^{N−1} ≤ gap ≤ X^0` iff `F̂(I) ≤ F ≤ F̄(I)`, and then both constant profiles
are Nash equilibria, they are the only ones, and every member earns strictly more when all
hedge. -/
theorem step_1_cases (m : Params) (hm : Standing m) (I F : ℝ) (hI : I ∈ Set.Icc 0 m.Ihat0)
    (hF : 0 ≤ F) (hFD : F ≤ m.D - I) :
    ((m.Accp - I - F) * m.pledge - (m.D - I - F) < m.X (m.N - 1) I F ↔ F < m.Fhat I) ∧
    (F < m.Fhat I → ∀ a : Fin m.N → Action, m.IsNash I F a ↔ a = fun _ => Action.r) ∧
    (m.X 0 I F < (m.Accp - I - F) * m.pledge - (m.D - I - F) ↔ m.Fbar I < F) ∧
    (m.Fbar I < F → ∀ a : Fin m.N → Action, m.IsNash I F a ↔ a = fun _ => Action.s) ∧
    ((m.X (m.N - 1) I F ≤ (m.Accp - I - F) * m.pledge - (m.D - I - F) ∧
        (m.Accp - I - F) * m.pledge - (m.D - I - F) ≤ m.X 0 I F) ↔
      m.Fhat I ≤ F ∧ F ≤ m.Fbar I) ∧
    (m.Fhat I ≤ F → F ≤ m.Fbar I →
      m.IsNash I F (fun _ => Action.r) ∧ m.IsNash I F (fun _ => Action.s) ∧
      (∀ a : Fin m.N → Action, m.IsNash I F a ↔
        a = (fun _ => Action.r) ∨ a = (fun _ => Action.s)) ∧
      ∀ i, m.payoff I F (fun _ => Action.r) i < m.payoff I F (fun _ => Action.s) i) := by sorry

end CCPCollateral.Incentive
