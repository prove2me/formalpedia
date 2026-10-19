-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_proposition_9
-- name    : DERAggregation.MarketPower.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:04.053716+00:00
-- url     : https://prove2.me/theorems/4a1eadfb-9b1a-4c40-8f63-54e78aab6c18
-- title:
--   Proposition 9, p. 34 — the four welfares relative to W_0, (88)–(91)
-- statement:
--   Consider the single-node market of §5 under Assumption 5. Let $\mathcal W_0=\sum_iu_i(C_i)$ (87), $z^T_i=-C_i+(\alpha-b_i)/(2a_i)$, $d^{TN}_i=[z^T_i]^+$, and $\lambda^T=\lambda^{TN}=\alpha$ (Propositions 5 and 7). For a strategic outcome with participation, with price $\lambda^S$ and net purchases $z^S$, put $\delta=\lambda^S-\lambda^T$; for one without participation, with price $\lambda^{SN}$ and purchases $d^{SN}$, put $\delta^N=\lambda^{SN}-\lambda^{TN}$. Then
--   $$\mathcal W^T=\mathcal W_0-\sum_ia_i(z^T_i)^2, \tag{88}$$
--   $$\mathcal W^S=\mathcal W_0+\sum_i\big(-a_i(z^S_i)^2+\delta z^S_i\big), \tag{89}$$
--   $$\mathcal W^{TN}=\mathcal W_0-\sum_ia_i(d^{TN}_i)^2=\mathcal W_0-\sum_{\{i\,:\,z^T_i>0\}}a_i(z^T_i)^2, \tag{90}$$
--   $$\mathcal W^{SN}=\mathcal W_0-\sum_ia_i(d^{SN}_i)^2+\delta^N\sum_id^{SN}_i, \tag{91}$$
--   where (89) holds at every strategic outcome with participation and (91) at every strategic outcome without participation.
--
--   These expressions put the four welfares on a common reference point, which is what makes them comparable.
--
--   **Formalization Note** The displayed formulas on p. 34 are formalized; the appendix's restatement of the last lines of (90) and (91) (p. 53) drops $a_i$ and a square, and is not followed. $\lambda^T=\lambda^{TN}=\alpha$ is substituted. Assumption 5 includes the readings H1, H2 of its informal clauses; the bid layer behind $\mathcal W^S,\mathcal W^{SN}$ is not modelled.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.3, p. 34, (87), Proposition 9, (88)–(91)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- Proposition 9 (p. 34). Under Assumption 5, with `W_0 = Σ_i u_i(C_i)` (87),
`z^T_i = −C_i + (α − b_i)/(2a_i)` (50), `d^{TN}_i = [z^T_i]^+` (70),
`λ^T = λ^{TN} = α`, `δ = λ^S − λ^T` and `δ^N = λ^{SN} − λ^{TN}`:
(88) `W^T = W_0 − Σ_i a_i (z^T_i)²`; (89) `W^S = W_0 + Σ_i (−a_i (z^S_i)² + δ z^S_i)` at every
strategic outcome with participation; (90) `W^{TN} = W_0 − Σ_i a_i (d^{TN}_i)² =
W_0 − Σ_{i : z^T_i > 0} a_i (z^T_i)²`; (91) `W^{SN} = W_0 − Σ_i a_i (d^{SN}_i)² + δ^N Σ_i d^{SN}_i` at
every strategic outcome without participation. -/
theorem proposition_9 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    WT a b C α N = W0 a b C - (∑ i, a i * zT a b C α i ^ 2) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      welS a b C α N z q = W0 a b C + ∑ i, (-(a i) * z i ^ 2 + (lam - α) * z i)) ∧
    WTN a b C α N = W0 a b C - (∑ i, a i * (max (zT a b C α i) 0) ^ 2) ∧
    WTN a b C α N =
      W0 a b C - (∑ i ∈ univ.filter (fun i => 0 < zT a b C α i), a i * zT a b C α i ^ 2) ∧
    (∀ (q lam : ℝ) (d : ι → ℝ), IsStratN a b C α N q lam d →
      welSN a b C α N d q = W0 a b C - (∑ i, a i * d i ^ 2) + (lam - α) * (∑ i, d i)) := by sorry

end DERAggregation.MarketPower
