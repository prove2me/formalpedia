-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_proposition_1_i
-- name    : FBAComp.AmazonGain.proposition_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:14.498565+00:00
-- url     : https://prove2.me/theorems/092204e1-b261-4f08-b81e-1e00c6509042
-- title:
--   Proposition 1 (i), p. 18 — seller fee threshold
-- statement:
--   At $\eta\in(0,\alpha)$, compare a no-FBA equilibrium with an FBA subgame outcome at fee $T$. If the seller's FBA sales are nonnegative, its profit strictly improves exactly when the fee is below the threshold $\bar T$:
--
--   $$\Pi_{S,N}^*<\Pi_{S,F}^*(T)\iff T<\bar T.$$
--
--   This is the seller's willingness-to-pay condition used by Amazon's fee problem.
--
--   **Formalization Note.** Positive no-FBA seller sales and nonnegative FBA seller sales are required to identify the economically relevant branch of the quadratic seller-profit identity.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 18, Proposition 1 (i); proof p. 37

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

namespace FBAComp.AmazonGain

/-- Proposition 1 (i), p. 18: with nonnegative seller sales, strict improvement
in the seller's profit holds exactly below the printed fee threshold. -/
theorem proposition_1_i (P : Params) (hP : P.Standing) (hI : Interior P)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN) (hF : IsSubgameEqF P η T wF pAF pSF)
    (hSales : 0 ≤ qSF P η pAF pSF) :
    profitSN P η pAN pSN < profitSF P η T pAF pSF ↔ T < Tbar P η := by sorry

end FBAComp.AmazonGain
