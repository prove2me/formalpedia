-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_proposition_1
-- name    : AssetDebt.ControlBand.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:56.661195+00:00
-- url     : https://prove2.me/theorems/57e35445-1850-45a7-b93a-08721cc42c9f
-- title:
--   Proposition 1(i) and recursion in (ii), p. 9, with (A.1) — without debt and capacity limits, sell everything once $P_t \ge R^o_t$; $R^o_t = \rho E_t \max\{P_{t+1}, R^o_{t+1}\}$
-- statement:
--   Assume there is no capacity constraint ($\ell = 1$) and no debt. Let $R^o_t = \rho\, E[U_{t+1}(1, P_{t+1}) \mid P_t]$ be the debt-free critical price. Then:
--
--   1. **Value (A.1).** For $1 \le t \le T$, $x \in [0,1]$ and $p > 0$,
--   $$U_t(x, p) = \max\{p,\ R^o_t\}\, x .$$
--   2. **Policy (i).** For $1 \le t \le T$, $x \in [0,1]$ and $p > 0$: if $p \ge R^o_t$, selling the entire remaining amount $x$ is optimal in the debt-free problem (1); if $p < R^o_t$, selling nothing is optimal. Hence the asset is sold all at once, in period $\tau^o = \inf\{t : P_t \ge R^o_t\}$.
--   3. **Recursion (ii).** For $p > 0$, $R^o_T(p) = 0$, and for $1 \le t \le T-1$,
--   $$R^o_t = \rho\, E_t \max\{P_{t+1},\ R^o_{t+1}\}.$$
--
--   This is the debt-free benchmark against which the effect of debt is measured: it generalizes Karlin's one-time stopping rule to a divisible asset with Markov prices.
--
--   **Formalization Note** "Optimal" means attaining the maximum of the objective $p\,q + \rho E_t U_{t+1}(x-q, P_{t+1})$ over $q \in [0, x]$; uniqueness is not claimed (at $p = R^o_t$ both quantities are optimal). The value identity (A.1) is taken from the proof of Proposition 1 (Online Appendix p. 2). The sentence of (ii) on $E_0 \rho^t R^o_t$ and part (iii) are not included.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), p. 9 (PDF 9), Proposition 1(i) and the recursion in (ii); Online Appendix p. 2 (PDF 34), (A.1)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Proposition 1(i) and the critical-price recursion in (ii), p. 9, with (A.1) from its proof (Online Appendix p. 2), without
capacity constraint (`ℓ = 1`) and without debt:
* (A.1) `U_t(x, p) = max{p, R^o_t} x`;
* (i) selling the entire remaining asset is optimal when `p ≥ R^o_t`, and selling nothing is
  optimal when `p < R^o_t` (so the asset is sold all at once at `τ° = inf{t : P_t ≥ R^o_t}`);
* (ii) `R^o_T = 0` and `R^o_t = ρ E_t max{P_{t+1}, R^o_{t+1}}` for `t = 1, …, T - 1`. -/
theorem proposition_1 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) :
    (∀ t, 1 ≤ t → t ≤ P.T → ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 < p →
        U P t x p = max p (Ro P t p) * x) ∧
    (∀ t, 1 ≤ t → t ≤ P.T → ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 < p →
        (Ro P t p ≤ p → IsOptimalU P t x p x) ∧ (p < Ro P t p → IsOptimalU P t x p 0)) ∧
    (∀ p : ℝ, 0 < p → Ro P P.T p = 0) ∧
    (∀ t, 1 ≤ t → t < P.T → ∀ p : ℝ, 0 < p →
        Ro P t p = P.ρ * ∫ p', max p' (Ro P (t + 1) p') ∂(P.κ t p)) := by sorry

end AssetDebt.ControlBand
