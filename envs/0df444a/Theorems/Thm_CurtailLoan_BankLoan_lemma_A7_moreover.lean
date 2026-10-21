-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_lemma_A7_moreover
-- name    : CurtailLoan.BankLoan.lemma_A7_moreover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:24.942328+00:00
-- url     : https://prove2.me/theorems/d5464210-d532-4ae9-adfe-bea174a049eb
-- title:
--   Lemma A.7 Moreover, Appendix p. 19 (PDF 52) — $t_k(w)$ decreases with $u$, increases with $\tau$, unimodal with maximum at $w_{min} \in (w^u_1, \hat w)$
-- statement:
--   Consider the model of the mission with a regular demand law. The buyer's additional revenue from insurance, $t_k(w)$ of (A-7), has the following properties.
--
--   1. **In $u$.** If $u_1 < u_2$ and the global assumptions and $u + l - \tau < \hat w \hat Q$ hold for every initial loan limit $u \in [u_1, u_2]$ (other parameters fixed), then for every $w$ lying in the interval $(w^u_1, w^u_2)$ of both $u_1$ and $u_2$,
--   $$t_k(w)\big|_{u = u_2} < t_k(w)\big|_{u = u_1}.$$
--   2. **In $\tau$.** If $\tau_1 < \tau_2$ and the same hypotheses hold for every fee in $[\tau_1, \tau_2]$, then $t_k(w)|_{\tau = \tau_1} < t_k(w)|_{\tau = \tau_2}$ for every $w$ in both intervals.
--   3. **In $w$.** Under the global assumptions and $u + l - \tau < \hat w\hat Q$, $w^u_1 < w_{min} < \hat w$, and $t_k$ is strictly increasing on $(w^u_1, w_{min}]$ and strictly decreasing on $[w_{min}, w^u_2)$; in particular $w_{min}$ is its unique maximizer.
--
--   The monotonicity in $u$ and $\tau$ drives the comparative statics of the equilibrium price $w^t_2$, and the unimodality is what makes $w^t_1 < w^t_2$ the two roots of $t_k(w) = t$.
--
--   **Formalization Note** "Decreases/increases" are strict, as the page's proof signs the derivatives strictly. The parametric claims are read along segments of parameters on which the hypotheses hold pointwise. The rest of the paragraph (the identification $w_{min} = w_b$ or $w_c$ through $v_b$, and $w_b > w^l_b$, $w_c > w^l_c$) is not formalized.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 19 (PDF 52), Lemma A.7, Moreover, first clauses

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Lemma A.7, "Moreover", first sentence, Appendix p. 19 (PDF 52): `tk(w)` strictly decreases
with `u`, strictly increases with `τ`, and is unimodal in `w` with its maximum at
`w_min ∈ (w^u_1, ŵ)`. -/
theorem lemma_A7_moreover (P : Params) (hR : P.Regular) :
    (∀ (u₁ u₂ w : ℝ), u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Global (P.withU x) ∧ RootsDefined (P.withU x)) →
      w ∈ Set.Ioo (wu1 (P.withU u₁)) (wu2 (P.withU u₁)) →
      w ∈ Set.Ioo (wu1 (P.withU u₂)) (wu2 (P.withU u₂)) →
      tk (P.withU u₂) w < tk (P.withU u₁) w) ∧
    (∀ (τ₁ τ₂ w : ℝ), τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Global (P.withTau x) ∧ RootsDefined (P.withTau x)) →
      w ∈ Set.Ioo (wu1 (P.withTau τ₁)) (wu2 (P.withTau τ₁)) →
      w ∈ Set.Ioo (wu1 (P.withTau τ₂)) (wu2 (P.withTau τ₂)) →
      tk (P.withTau τ₁) w < tk (P.withTau τ₂) w) ∧
    (Global P → RootsDefined P →
      wu1 P < wmin P ∧ wmin P < what P ∧
      StrictMonoOn (tk P) (Set.Ioc (wu1 P) (wmin P)) ∧
      StrictAntiOn (tk P) (Set.Ico (wmin P) (wu2 P))) := by sorry

end CurtailLoan.BankLoan
