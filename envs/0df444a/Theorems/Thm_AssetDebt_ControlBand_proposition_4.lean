-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_proposition_4
-- name    : AssetDebt.ControlBand.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:01.406927+00:00
-- url     : https://prove2.me/theorems/c939105c-4e72-41a5-be71-6bc5f08763d3
-- title:
--   Proposition 4, p. 14 — single debt payment at $m < T$: the first sale follows a control band $R^{(1)}_t \le R^{(2)}_t$, and the sign of $E_t\Delta_{t+1}$ decides expedited vs delayed selling
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $D > 0$ due at the end of period $m$, with $1 \le m < T$. Let $R^{(1)}_t$ and $R^{(2)}_t$ be the critical prices of (A.10), $R^o_t$ the debt-free critical price (4), $E_t\Delta_{t+1}$ the expected net effect of debt (5), and $\delta = \rho^{m-t} D$. Fix a period $1 \le t \le m$ in which no asset has been sold yet (inventory $1$, working capital $0$) and a price $p > 0$. Then:
--
--   **(i) Control band.** $R^{(1)}_t \le R^{(2)}_t$, and
--
--   1. if $p < R^{(1)}_t$: for $t < m$ selling nothing is optimal; for $t = m$ no quantity is feasible, so the seller goes bankrupt at the end of period $m$;
--   2. if $R^{(1)}_t \le p < R^{(2)}_t$: selling $q = \delta/p$, whose revenue secures the debt, is optimal; afterwards, in every period $s$ with $t < s \le m$, at every inventory $x \in [0,1]$, working capital $w \ge \rho^{m-s} D$ and price $p' > 0$, the optimal quantities are exactly those of the debt-free problem (1), so the remaining asset is sold at $\tau' = \inf\{s > t : P_s \ge R^o_s\}$;
--   3. if $p \ge R^{(2)}_t$: selling the entire asset is optimal.
--
--   Consequently the first sale happens at $\tau = \inf\{t \le m : P_t \ge R^{(1)}_t\}$.
--
--   **(ii) Expedited versus delayed selling.**
--
--   $$E_t\Delta_{t+1} < 0 \;\Rightarrow\; R^{(1)}_t < R^{(2)}_t = R^o_t, \qquad E_t\Delta_{t+1} \ge 0 \;\Rightarrow\; R^{(1)}_t = R^{(2)}_t \ge R^o_t,$$
--
--   and if $E_t\Delta_{t+1} = 0$ then $R^{(1)}_t = R^{(2)}_t = R^o_t$.
--
--   When the bankruptcy cost dominates the value of limited liability, part of the asset is sold earlier than without debt; when limited liability dominates, selling is delayed and done all at once.
--
--   **Formalization Note** The page asserts that "there exist two series of critical prices"; since these depend on the current price, the statement uses the explicit thresholds the paper's proof constructs in (A.10), not a free existential. "Optimal" means feasible and attaining the maximum of the period-$t$ objective of (2)–(3); uniqueness is not claimed. The stopping-time statement is rendered by the per-period optimal actions at the no-prior-sale state; after the debt-securing sale, periods after $m$ are governed by the debt-free problem by definition. Prices are assumed almost surely positive, which the paper needs to divide by $p_t$.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), p. 14 (PDF 14), Proposition 4; Online Appendix p. 8 (PDF 40), (A.10)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Proposition 4, p. 14: a single debt payment `d_m = D > 0` at `m < T`, no capacity
constraint (`ℓ = 1`). In every period `t ≤ m` before the first sale (state `x = 1`, `w = 0`),
with the critical prices `R^{(1)}_t ≤ R^{(2)}_t` of (A.10) and `δ = ρ^{m-t} d_m`:
* (i) below `R^{(1)}_t` do not sell (`t < m`), resp. the seller is bankrupt (`t = m`); between the
  critical prices selling `δ/p` is optimal, and afterwards (debt secured) the optimal quantities
  are exactly the debt-free ones; at or above `R^{(2)}_t` selling the entire asset is optimal;
* (ii) if `E_t Δ_{t+1} < 0` then `R^{(1)}_t < R^{(2)}_t = R^o_t`; if `E_t Δ_{t+1} ≥ 0` then
  `R^{(1)}_t = R^{(2)}_t ≥ R^o_t`; if `E_t Δ_{t+1} = 0` then `R^{(1)}_t = R^{(2)}_t = R^o_t`. -/
theorem proposition_4 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (D : ℝ) (hD : 0 < D)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m) (p : ℝ) (hp : 0 < p) :
    R1 P m D t p ≤ R2 P m D t p ∧
    (p < R1 P m D t p →
        (t < m → IsOptimal P (singlePayment m D) m t 1 0 p 0) ∧
        (t = m → ∀ q, ¬ Feasible P (singlePayment m D) m 1 0 p q)) ∧
    (R1 P m D t p ≤ p → p < R2 P m D t p →
        IsOptimal P (singlePayment m D) m t 1 0 p (P.ρ ^ (m - t) * D / p) ∧
        ∀ s, t < s → s ≤ m → ∀ x w p' : ℝ, 0 ≤ x → x ≤ 1 → P.ρ ^ (m - s) * D ≤ w → 0 < p' →
          ∀ q, IsOptimal P (singlePayment m D) m s x w p' q ↔ IsOptimalU P s x p' q) ∧
    (R2 P m D t p ≤ p → IsOptimal P (singlePayment m D) m t 1 0 p 1) ∧
    (EDelta P m D t p < 0 → R1 P m D t p < R2 P m D t p ∧ R2 P m D t p = Ro P t p) ∧
    (0 ≤ EDelta P m D t p → R1 P m D t p = R2 P m D t p ∧ Ro P t p ≤ R2 P m D t p) ∧
    (EDelta P m D t p = 0 → R1 P m D t p = Ro P t p ∧ R2 P m D t p = Ro P t p) := by sorry

end AssetDebt.ControlBand
