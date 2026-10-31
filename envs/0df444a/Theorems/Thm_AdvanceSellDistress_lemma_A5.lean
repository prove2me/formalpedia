-- Prove2me | Theorems.Thm_AdvanceSellDistress_lemma_A5
-- name    : AdvanceSellDistress.lemma_A5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:23.511001+00:00
-- url     : https://prove2.me/theorems/386d1c27-7b3c-4a4c-8174-d4ef4bc08b13
-- title:
--   Lemma A.5: financing when all inner consumers hold coupons — high-price, low-price and no-financing cases
-- statement:
--   Let $p_s\in[0,1]$ and $p_a\in\mathbb R$, and suppose all inner consumers have bought the coupon $(p_a,p_s)$. Write $S=p_s+m_o$, so the firm's revenue is $S$ after success and $\lambda S$ after no success, and it borrows $L=\max(I-p_a,0)$ from the competitive bank. Let
--   $$p^h_{bb}(p_s)=I-\beta\lambda S,\qquad p^l_{bb}(p_s)=I-\beta\Big[\lambda S+\frac{(1-\lambda)^2S^2}{8a}\Big].$$
--
--   1. **High-price strategy.** If $p_a\ge p^h_{bb}(p_s)$, financing is secured. Every outcome has effort $e^h_{bb}(p_s)=(1-\lambda)S/(2a)$ and profit
--   $$\pi^h_{bb}(p_a,p_s)=\beta\Big[\frac{(1-\lambda)^2S^2}{4a}+\lambda S\Big]+p_a-I .$$
--   If $p_a\ge I$ there is no loan (face value $0$). Otherwise the face value is $(I-p_a)(1+r^h_{bb})$ with $r^h_{bb}=1/\beta-1$.
--   2. **Low-price strategy.** If $p^l_{bb}(p_s)\le p_a<p^h_{bb}(p_s)$, financing is secured. Every outcome has effort
--   $$e^l_{bb}(p_a,p_s)=\frac{(1-\lambda)S+\sqrt{(1-\lambda)^2S^2-8a[(I-p_a)/\beta-\lambda S]}}{4a},$$
--   profit $\beta a\,e^l_{bb}(p_a,p_s)^2$, and face value $(I-p_a)(1+r^l_{bb}(p_a,p_s))$, where
--   $$r^l_{bb}(p_a,p_s)=\frac{(1+\lambda)S-\sqrt{(1-\lambda)^2S^2-8a[(I-p_a)/\beta-\lambda S]}}{2(I-p_a)}-1 .$$
--   3. If $0<p_a<p^l_{bb}(p_s)$, no face value breaks even: financing fails.
--
--   The lemma solves the firm–bank subgame behind every coupon plan. It splits plans into the safe-loan (high-price) and risky-loan (low-price) regimes that the analysis of the hybrid scheme optimizes over.
--
--   **Formalization Note** The outcome (`HAllBuyOutcome`) is the least break-even face value together with the best-response effort on $[0,1]$. The profit is $\max(p_a-I,0)+\beta U(e;D)$.
--
--   Differences from the source:
--   - reading: Lemma A.5 for any spot price p_s → p_s ∈ [0,1]; reason: the coupon spot prices of the paper's schemes range over [0,1] ((131), p. 78); for larger p_s the printed effort (1 − λ)(p_s + m_o)/(2a) can exceed 1 and the lemma is false
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: interest rate r → face value D = L(1 + r), the least break-even face value (the paper's smaller root); reason: r = D/L − 1; same instances
--   - encoding: if p_a ≥ I the firm obtains financing solely through advance selling → the face value is 0; reason: with L = 0 the least break-even face value is 0
--   - encoding: the firm fails to secure financing → no face value D ≥ 0 breaks even; reason: the loan is granted iff some face value breaks even
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, Lemma A.5, pp.32–33 (PDF 33–34)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Lemma A.5** of Papanastasiou–Xiao–Yang, *Advance Selling to Ease Financial Distress*,
Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, pp. 32–33 (PDF 33–34): the
financing subgame when all inner consumers hold the coupon `(p_a, p_s)`.
With `S = p_s + m_o`, revenues `S` (success) and `λ S` (no success) and loan
`L = max(I − p_a, 0)`:

1. (high-price strategy) if `p_a ≥ p^h_bb(p_s)`, financing is secured, and every outcome has effort
   `e^h_bb(p_s)` and profit `π^h_bb(p_a, p_s)`; if `p_a ≥ I` there is no loan (face value `0`),
   otherwise the face value is `(I − p_a)(1 + r^h_bb)` with `r^h_bb = 1/β − 1`;
2. (low-price strategy) if `p^l_bb(p_s) ≤ p_a < p^h_bb(p_s)`, financing is secured, and every outcome
   has effort `e^l_bb(p_a, p_s)`, profit `β a e^l_bb(p_a, p_s)²` and face value
   `(I − p_a)(1 + r^l_bb(p_a, p_s))`;
3. if `0 < p_a < p^l_bb(p_s)`, no face value breaks even: financing fails.

**Formalization Note.** `p_s ∈ [0, 1]` (the coupon spot prices of the paper, the domain of (131));
with Assumption 1 this keeps every effort in `[0, 1]`. Effort and face value are the best response
and the least break-even face value (`HAllBuyOutcome`). -/
theorem lemma_A5 (P : Params) (hP : P.Standing) (pa ps : ℝ) (hps : ps ∈ Set.Icc (0 : ℝ) 1) :
    (P.ph_bb ps ≤ pa →
      (∃ D e, P.HAllBuyOutcome pa ps D e) ∧
      ∀ D e, P.HAllBuyOutcome pa ps D e →
        e = P.eh_bb ps ∧
          P.firmProfit (ps + P.mo) (P.lam * (ps + P.mo)) pa D e = P.pih_bb pa ps ∧
          (P.I ≤ pa → D = 0) ∧ (pa < P.I → D = (P.I - pa) * (1 + P.rFB))) ∧
    (P.pl_bb ps ≤ pa → pa < P.ph_bb ps →
      (∃ D e, P.HAllBuyOutcome pa ps D e) ∧
      ∀ D e, P.HAllBuyOutcome pa ps D e →
        e = P.el_bb pa ps ∧
          P.firmProfit (ps + P.mo) (P.lam * (ps + P.mo)) pa D e =
            P.β * P.a * P.el_bb pa ps ^ 2 ∧
          D = (P.I - pa) * (1 + P.rl_bb pa ps)) ∧
    (0 < pa → pa < P.pl_bb ps →
      ¬ ∃ D, P.BreaksEven (ps + P.mo) (P.lam * (ps + P.mo)) (max (P.I - pa) 0) D) := by sorry

end AdvanceSellDistress
