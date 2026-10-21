-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_proposition_2_2
-- name    : CurtailLoan.BankLoan.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:35.275123+00:00
-- url     : https://prove2.me/theorems/60a50204-60c5-45cb-8b13-8a31093bba96
-- title:
--   Proposition 2 part 2, p. 14 (PDF 14) — in Area II a lower initial loan limit and a higher fixed bank fee benefit the supplier
-- statement:
--   Consider the model of the mission with a regular demand law: a capital-constrained buyer with initial capital $l$ finances its newsvendor order through a bank loan (initial loan limit $u$, fixed fee $\tau$) and possibly loan insurance (insured loan limit $v$, fixed premium $t$), and a supplier with unit cost $c$ sets the wholesale price; $\Pi^{I*}_S$ and $\Pi^{I*}_B$ are the supplier's and the buyer's profits in a goodwill Stackelberg equilibrium. Assume bank financing with loan insurance with $u + l - \tau < w^E Q^E$ and $v > u$ (together with the paper's global assumptions), and that the fixed insurance premium is in the middle range (Area II):
--   $$t_k(w_I) < t \le t_k(w_{II}).$$
--
--   1. $\Pi^{I*}_S$ strictly decreases with $u$, whereas $\Pi^{I*}_B$ strictly increases with $u$: a lower initial loan limit benefits the supplier.
--   2. $\Pi^{I*}_B$ strictly decreases with $\tau$; and if $v + l - \tau - t \ge w^t_2\bar F^{-1}(w^t_2)$, then $\Pi^{I*}_S$ strictly increases with $\tau$: a higher fixed bank fee benefits the supplier.
--
--   Precisely: for $u_1 < u_2$ such that the assumptions and Area II hold at every $u \in [u_1, u_2]$ (other parameters fixed), and any equilibria at $u_1$ and at $u_2$,
--   $$\Pi^{I*}_S(u_2) < \Pi^{I*}_S(u_1), \qquad \Pi^{I*}_B(u_1) < \Pi^{I*}_B(u_2);$$
--   for $\tau_1 < \tau_2$ such that the assumptions and Area II hold at every $\tau \in [\tau_1, \tau_2]$, and any equilibria at $\tau_1$ and $\tau_2$, $\Pi^{I*}_B(\tau_2) < \Pi^{I*}_B(\tau_1)$, and if moreover the insured loan limit does not bind at $w^t_2$ for every $\tau \in [\tau_1, \tau_2]$, then $\Pi^{I*}_S(\tau_1) < \Pi^{I*}_S(\tau_2)$.
--
--   This is the paper's "beneficial curtailment of bank loan": contrary to the intuition that more credit and cheaper credit help every firm, in the insurance-cooperation region the supplier gains when the bank lends less or charges more, because a tighter loan forces the buyer to rely on insurance, which the supplier encourages by cutting its price less.
--
--   **Formalization Note** "Decreases/increases" are read as strict monotonicity along every parameter segment on which the hypotheses hold pointwise (Area II moves with $u$ and $\tau$). The condition of part (ii) applies to $\Pi^{I*}_S$ only, as on the page; the claim on $\Pi^{I*}_B$ is unconditional. $\Pi^{I*}$ is the profit at any equilibrium; existence and uniqueness of the equilibrium in Area II is Proposition 1 item 1(b), a milestone.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), p. 14 (PDF 14), Proposition 2 part 2

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Proposition 2 part 2, p. 14 (PDF 14): in Area II (i) the supplier's equilibrium profit
strictly decreases and the buyer's strictly increases with the initial loan limit `u`; (ii) the
buyer's equilibrium profit strictly decreases with the fixed bank fee `τ`, and, where the insured
loan limit does not bind at `w^t_2`, the supplier's strictly increases with `τ`. -/
theorem proposition_2_2 (P : Params) (hR : P.Regular) :
    (∀ u₁ u₂ : ℝ, u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x) ∧ AreaII (P.withU x)) →
      ∀ o₁ o₂ : Outcome, IsEquilibrium (P.withU u₁) o₁ → IsEquilibrium (P.withU u₂) o₂ →
        PiS (P.withU u₂) o₂ < PiS (P.withU u₁) o₁ ∧
        PiB (P.withU u₁) o₁ < PiB (P.withU u₂) o₂) ∧
    (∀ τ₁ τ₂ : ℝ, τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Standing (P.withTau x) ∧ AreaII (P.withTau x)) →
      ∀ o₁ o₂ : Outcome, IsEquilibrium (P.withTau τ₁) o₁ → IsEquilibrium (P.withTau τ₂) o₂ →
        PiB (P.withTau τ₂) o₂ < PiB (P.withTau τ₁) o₁ ∧
        ((∀ x ∈ Set.Icc τ₁ τ₂, InsuredSlack (P.withTau x)) →
          PiS (P.withTau τ₁) o₁ < PiS (P.withTau τ₂) o₂)) := by sorry

end CurtailLoan.BankLoan
