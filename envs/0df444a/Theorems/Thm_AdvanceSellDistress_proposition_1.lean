-- Prove2me | Theorems.Thm_AdvanceSellDistress_proposition_1
-- name    : AdvanceSellDistress.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:13.437717+00:00
-- url     : https://prove2.me/theorems/ea6f3308-db0f-49fd-b9d0-66d40ee94ac8
-- title:
--   Proposition 1: bank-only benchmark — first best for $I\le I_l$, smaller-root risky loan for $I_l<I\le I_h$, credit rationing for $I>I_h$
-- statement:
--   Consider the model without advance selling: the firm borrows its whole funding need $I$ from a competitive bank, then chooses its regular price and effort. Assume Assumptions 1–2.
--
--   **Price.** In each state (valuation probability $\lambda_z\in\{1,\lambda\}$) the regular price
--   $$p^*_r=\begin{cases}v,&v\ge1+m_o,\\1,&\text{otherwise}\end{cases}$$
--   maximizes the repayment-period revenue, whose maximum is $\lambda_zv_m$. When $v\ne1+m_o$ it is the only maximizer.
--
--   1. If $I\le I_l$, the bank lends. Every equilibrium has face value $I(1+r^*_{FB})$ with $r^*_{FB}=1/\beta-1$, effort $e^*_{FB}=(1-\lambda)v_m/(2a)$ and profit $\pi^*_{FB}=\beta[(1-\lambda)^2v_m^2/(4a)+\lambda v_m]-I$.
--   2. If $I_l<I\le I_h$, the bank lends. Every equilibrium has face value $I(1+r^*_B)$, effort $e^*_B$ and profit $\pi^*_B=\beta a(e^*_B)^2$, where
--   $$r^*_B=\frac{(1+\lambda)v_m-\sqrt{(1-\lambda)^2v_m^2-8a(I/\beta-\lambda v_m)}}{2I}-1,\qquad e^*_B=\frac{(1-\lambda)v_m+\sqrt{(1-\lambda)^2v_m^2-8a(I/\beta-\lambda v_m)}}{4a}.$$
--   Moreover $r^*_B\ge r^*_{FB}$, $e^*_B\le e^*_{FB}$ and $\pi^*_B\le\pi^*_{FB}$.
--   3. If $I>I_h$, no face value breaks even: the firm is credit-rationed and goes bankrupt.
--
--   This is the benchmark that every advance-selling scheme is compared with. Its effort $e^*_B$ fixes the consumers' outside option under the all-or-nothing clause, and its profit is the bar the hybrid scheme must beat.
--
--   **Formalization Note** An equilibrium (`BankOutcome`) is a pair $(D,e)$: $D$ is the least face value at which the bank breaks even, and $e$ is the firm's best-response effort on $[0,1]$. The interest rate is $r=D/I-1$. "Every equilibrium" makes the stated values unique, and the existence clause makes the statement non-vacuous.
--
--   Differences from the source:
--   - reading: the equilibrium selling price is p*_r = v if v ≥ 1 + m_o, 1 otherwise → that price attains the maximal revenue λ_z v_m in both states, and is the unique maximizer when v ≠ 1 + m_o; reason: at v = 1 + m_o both v and 1 give revenue λ_z v_m, so the printed v is a tie-break (the proof of Proposition A.7 uses 1 there)
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: interest rate r → face value D = L(1 + r), the least break-even face value (the paper's smaller root); reason: r = D/L − 1; same instances
--   - encoding: (iii) the firm fails to secure a bank loan and goes bankrupt → no face value D ≥ 0 breaks even; reason: the loan is granted iff some face value breaks even
--   - encoding: the firm sets the revenue-maximizing regular price in the repayment period → the financing subgame uses the revenues at that price (v_m, λ v_m bank-only; p_s + m_o, λ(p_s + m_o) with coupons); reason: that the price is revenue-maximizing is proved in Proposition 1's price clause and Proposition 10's clause (0)
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, Proposition 1, pp.7–8 (PDF 8–9); proof, eqs. (1)–(7), pp.34–35 (PDF 35–36)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Proposition 1** of Papanastasiou–Xiao–Yang, *Advance Selling to Ease Financial Distress*,
Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, pp. 7–8 (PDF 8–9): the bank-only
benchmark.

* *Price.* In each state (`λ_z ∈ {1, λ}`) the regular price `v` (if `v ≥ 1 + m_o`) or `1`
  (otherwise) maximizes the repayment-period revenue, whose maximum is `λ_z v_m`; it is the unique
  maximizer when `v ≠ 1 + m_o`.
* (i) If `I ≤ I_l`, the bank lends (an outcome exists), and every outcome has face value
  `I (1 + r*_FB)`, effort `e*_FB` and profit `π*_FB`.
* (ii) If `I_l < I ≤ I_h`, the bank lends, every outcome has face value `I (1 + r*_B)`, effort `e*_B`
  and profit `π*_B = β a (e*_B)²`, and `r*_B ≥ r*_FB`, `e*_B ≤ e*_FB`, `π*_B ≤ π*_FB`.
* (iii) If `I > I_h`, no face value breaks even: the firm is credit-rationed and goes bankrupt.

**Formalization Note.** Effort is the best response on `[0, 1]` and the face value the least
break-even one (`BankOutcome`); the interest rate `r` enters through the face value `D = I (1 + r)`.
At `v = 1 + m_o` both prices are revenue-maximizing; the printed `p*_r = v` is a tie-break. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∀ lz ∈ ({1, P.lam} : Set ℝ),
      P.bankRevenue lz (if 1 + P.mo ≤ P.v then P.v else 1) = lz * P.vm ∧
      (∀ pr, P.bankRevenue lz pr ≤ lz * P.vm) ∧
      (P.v ≠ 1 + P.mo → ∀ pr, P.bankRevenue lz pr = lz * P.vm →
        pr = if 1 + P.mo ≤ P.v then P.v else 1)) ∧
    (P.I ≤ P.Il →
      (∃ D e, P.BankOutcome D e) ∧
      ∀ D e, P.BankOutcome D e →
        D = P.I * (1 + P.rFB) ∧ e = P.eFB ∧
          P.firmProfit P.vm (P.lam * P.vm) 0 D e = P.piFB) ∧
    (P.Il < P.I → P.I ≤ P.Ih →
      (∃ D e, P.BankOutcome D e) ∧
      (∀ D e, P.BankOutcome D e →
        D = P.I * (1 + P.rB) ∧ e = P.eB ∧
          P.firmProfit P.vm (P.lam * P.vm) 0 D e = P.piB) ∧
      P.rFB ≤ P.rB ∧ P.eB ≤ P.eFB ∧ P.piB ≤ P.piFB) ∧
    (P.Ih < P.I → ¬ ∃ D, P.BreaksEven P.vm (P.lam * P.vm) P.I D) := by sorry

end AdvanceSellDistress
