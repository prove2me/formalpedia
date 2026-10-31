-- Prove2me | Theorems.Thm_AdvanceSellDistress_proposition_10
-- name    : AdvanceSellDistress.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:20.368563+00:00
-- url     : https://prove2.me/theorems/1e6611c4-aa51-4807-8fbd-21c0c7fd399c
-- title:
--   Proposition 10: with $m_o=1$, $v\in(1,2)$, the hybrid coupon scheme H is optimal with explicit prices iff $I>I_m$ and $v\ge\underline w^l_H$; otherwise pure bank financing
-- statement:
--   Suppose $I_l<I\le I_h$, $m_o=1$ and $1<v<2$, under Assumptions 1–2. Let
--   $$R=(1-\lambda)^2-2a\Big(\frac I\beta-2\lambda\Big),\qquad \underline w^l_H=1+\frac{2\sqrt R}{1-\lambda},\qquad I_m=\beta\Big[2\lambda+\frac{3(1-\lambda)^2}{8a}\Big].$$
--   Consider advance selling with discount coupons $(p_a,p_s)$ and an all-or-nothing clause (scheme H).
--
--   0. $I_l<I_m<I_h$. For every spot price $p_s\in[0,1]$ and in both states, the regular price $p^{l*}_{rH}=1$ is the unique revenue-maximizing price among $p_r\ge p_s$, with revenue $\lambda_z(p_s+1)$. The price $1$ is also the unique revenue-maximizing bank-only price.
--   1. If $I>I_m$ and $v\ge\underline w^l_H$, the firm conducts hybrid advance selling. Let
--   $$p^{l*}_{sH}=v-1-\frac{\sqrt R}{1-\lambda},\qquad p^{l*}_{aH}=I-\beta\lambda(p^{l*}_{sH}+1),\qquad e^{l*}_H=\frac{(1-\lambda)(p^{l*}_{sH}+1)}{2a},\qquad \pi^{l*}_H=\beta a(e^{l*}_H)^2 .$$
--   Then:
--      1. the plan $(p^{l*}_{aH},p^{l*}_{sH})$ is feasible with effort $e^{l*}_H$ and profit $\pi^{l*}_H$;
--      2. no feasible plan earns more than $\pi^{l*}_H$;
--      3. every feasible plan earning $\pi^{l*}_H$ has effort $e^{l*}_H$;
--      4. the bank-only profit $\pi_B$ satisfies $\pi_B\le\pi^{l*}_H$, with strict inequality iff $v>\underline w^l_H$.
--   2. Otherwise, the firm uses pure bank financing: there is a bank-only equilibrium, and no feasible plan earns more than its profit $\pi_B$.
--
--   The proposition is the paper's main result on the hybrid scheme. Under moderate distress, coupons sold with an all-or-nothing clause beat bank financing exactly when distress is high enough ($I>I_m$) and inner consumers value the service enough ($v\ge\underline w^l_H$). The profit is then $\beta a(e^{l*}_H)^2$.
--
--   **Formalization Note** A feasible plan (`HPlan`) is a coupon plan with $p_a\in\mathbb R$ and $p_s\in[0,1]$ whose all-buy financing is secured (least break-even face value, best-response effort), and which the inner consumers buy (Lemma A.1 with the all-or-nothing deviation utilities). The bank-only profit $\pi_B$ is that of the bank-only equilibrium relation (`BankBenchmark`).
--
--   Differences from the source:
--   - reading: the equilibrium prices are given by p^{l*}_{rH} = 1, p^{l*}_{sH}, p^{l*}_{aH} → the plan (p^{l*}_{aH}, p^{l*}_{sH}) is an optimal feasible plan; effort and profit are unique over optimal plans; reason: the optimal plan is not unique: a risky-loan plan at other prices (case (i) of the low-price analysis, (144)) earns the same profit with the same effort
--   - reading: (i) the firm conducts hybrid advance selling; (ii) the firm uses pure bank financing → (i) the H optimum is ≥ π_B, strictly iff v > w^l_H; (ii) every feasible H plan earns ≤ π_B; reason: at v = w^l_H the two tie (π^{l*}_H = π_B); the paper resolves the tie as "conducts"
--   - reading: p. 9 requires waiting to give "lower" utility → Lemma A.1's weak inequalities define the purchasing equilibrium; reason: Lemma A.1 and (127) use ≥; with the strict form the optimum, which binds the constraint, is not attained
--   - reading: coupon plans (p_a, p_s) → p_a ∈ ℝ, p_s ∈ [0,1]; reason: the domain of (131); the paper does not restrict the sign of p_a
--   - encoding: the regular price p_r chosen by the firm in the repayment period → the financing subgame uses the revenues at the revenue-maximizing price 1; reason: clause (0) proves that 1 is the unique revenue-maximizing price
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, Proposition 10 and the definitions of w^l_H and I_m before it, p.21 (PDF 22); proof p.51 (PDF 52) via Proposition A.7 p.31 (PDF 32) and its proof pp.78–85 (PDF 79–86)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Proposition 10** of Papanastasiou–Xiao–Yang, *Advance Selling to Ease Financial Distress*,
Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, p. 21 (PDF 22). Suppose
`I_l < I ≤ I_h`, `m_o = 1` and `v ∈ (1, 2)`. Under advance selling with discount coupons and an
all-or-nothing clause ("H"):

0. `I_l < I_m < I_h`; for every spot price `p_s ∈ [0, 1]` and both states, the regular price
   `p^{l*}_{rH} = 1` is the unique revenue-maximizing price among `p_r ≥ p_s` (revenue
   `λ_z (p_s + 1)`), and `1` is also the unique revenue-maximizing bank-only price;
1. if `I > I_m` and `v ≥ w^l_H`, the firm conducts hybrid advance selling: the plan
   `(p^{l*}_{aH}, p^{l*}_{sH})` is feasible with effort `e^{l*}_H` and profit `π^{l*}_H = β a (e^{l*}_H)²`,
   no feasible plan earns more, every feasible plan earning `π^{l*}_H` has effort `e^{l*}_H`, and the
   bank-only profit `π_B` satisfies `π_B ≤ π^{l*}_H`, strictly iff `v > w^l_H`;
2. otherwise, the firm uses pure bank financing: no feasible plan earns more than `π_B`.

**Formalization Note.** A feasible plan (`HPlan`) is a coupon plan `p_a ∈ ℝ`, `p_s ∈ [0, 1]` whose
all-buy financing is secured (least break-even face value, best-response effort) and which the
inner consumers buy (Lemma A.1, weak inequalities, all-or-nothing deviation utilities). The optimal
prices are not unique; effort and profit are. At `v = w^l_H` the hybrid scheme and bank financing
tie. -/
theorem proposition_10 (P : Params) (hP : P.Standing) (hmo : P.mo = 1) (hv1 : 1 < P.v)
    (hv2 : P.v < 2) (hIl : P.Il < P.I) (hIh : P.I ≤ P.Ih) :
    (P.Il < P.Im ∧ P.Im < P.Ih) ∧
    (∀ lz ∈ ({1, P.lam} : Set ℝ), ∀ ps ∈ Set.Icc (0 : ℝ) 1,
      P.couponRevenue lz ps 1 = lz * (ps + P.mo) ∧
      ∀ pr, ps ≤ pr → pr ≠ 1 → P.couponRevenue lz ps pr < P.couponRevenue lz ps 1) ∧
    (∀ lz ∈ ({1, P.lam} : Set ℝ),
      P.bankRevenue lz 1 = lz * P.vm ∧
      ∀ pr, pr ≠ 1 → P.bankRevenue lz pr < P.bankRevenue lz 1) ∧
    (P.Im < P.I → P.wH ≤ P.v →
      P.HPlan P.paH P.psH P.eH P.piH ∧
      (∀ pa ps e π, P.HPlan pa ps e π → π ≤ P.piH) ∧
      (∀ pa ps e, P.HPlan pa ps e P.piH → e = P.eH) ∧
      ∃ πB uB, P.BankBenchmark πB uB ∧ πB ≤ P.piH ∧ (πB < P.piH ↔ P.wH < P.v)) ∧
    (¬ (P.Im < P.I ∧ P.wH ≤ P.v) →
      ∃ πB uB, P.BankBenchmark πB uB ∧ ∀ pa ps e π, P.HPlan pa ps e π → π ≤ πB) := by sorry

end AdvanceSellDistress
