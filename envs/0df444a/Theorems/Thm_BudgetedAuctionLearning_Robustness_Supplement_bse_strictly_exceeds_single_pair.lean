-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_Supplement_bse_strictly_exceeds_single_pair
-- name    : BudgetedAuctionLearning.Robustness.Supplement.bse_strictly_exceeds_single_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:31.244206+00:00
-- url     : https://prove2.me/theorems/fbd74400-e542-4ab4-8382-294d10b5818d
-- title:
--   Theorem 2.3 — the BSE value can strictly exceed the single-pair Stackelberg value
-- statement:
--   For a finite budgeted game $G=(U_O,U_L,P_O)$ and an optimizer budget $\rho$, let $\mathrm{SE}_G(\rho)$ be the largest optimizer utility $x^\top U_O y$ achievable by a single pair of mixed strategies $(x,y)$ with $y$ a learner best response to $x$ and expected payment $x^\top P_O y\le\rho$, and let $\mathrm{BSE}_G(\rho)$ be the value of program (2), where the optimizer may randomize over such pairs according to any probability law $\nu$ and the budget need only hold in expectation over $\nu$.
--
--   The theorem asserts that randomizing over pairs can be strictly more profitable: there exist a finite game $G$ and a budget $\rho$ with
--   $$
--   \mathrm{SE}_G(\rho)\;<\;\mathrm{BSE}_G(\rho).
--   $$
--
--   This separation is why the paper measures manipulability against the BSE value rather than the classical Stackelberg value: a budgeted optimizer may switch strategies for budget reasons alone.
--
--   **Formalization Note** Games have finite action sets $\mathrm{Fin}\,n_O$, $\mathrm{Fin}\,n_L$ and real matrices; the learner has no budget and best responds to the optimizer's mixed strategy, with all tied maximizers allowed. Both values are $\overline{\mathbb R}$-valued suprema.
--
--   Differences from the source:
--   - encoding: strategy spaces A, B and a best-response function BR left abstract (the claim is existential) → finite action sets Fin nO, Fin nL, real matrices U_O, U_L, P_O, and the unconstrained learner best response; reason: a witness in this class is a witness of the source's existential claim, and it is the class of the source's own illustrative example (printed pp. 5–6), so no instance of the source's claim is lost
--   - encoding: max in Eq. (1) and sup over ν ∈ Δ(Δ(A)×Δ(B)) in (2) → EReal suprema over the feasible pairs and over Borel probability measures on the product of the simplices with integrable integrands; reason: Lean convention; an infeasible program gives ⊥ instead of a default value, and integrability always holds for these bounded continuous integrands
-- source:
--   Giannis Fikioris, Éva Tardos, Balasubramanian Sivan, Learning vs. Optimizing Bidders in Budgeted Auctions, STOC 2027 submission #310 (October 2026), Theorem 2.3, printed p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_Supplement_BudgetedGame

set_option autoImplicit false

namespace BudgetedAuctionLearning.Robustness.Supplement

/-- Theorem 2.3 (Fikioris, Tardos, Sivan, STOC 2027 submission #310, printed p. 7, PDF p. 8):
the value of a BSE can be strictly more than the value of a Stackelberg equilibrium, i.e. of
program (2) restricted to a single pair. There is a finite budgeted game and a budget `ρ` with
`SE(ρ) < BSE(ρ)`. -/
theorem bse_strictly_exceeds_single_pair :
    ∃ (nO nL : ℕ) (G : BudgetedGame nO nL) (ρ : ℝ), G.SE ρ < G.BSE ρ := by sorry

end BudgetedAuctionLearning.Robustness.Supplement
