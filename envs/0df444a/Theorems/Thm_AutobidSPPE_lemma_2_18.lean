-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_18
-- name    : AutobidSPPE.lemma_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:11:39.263442+00:00
-- url     : https://prove2.me/theorems/6d596ff8-28d3-47e5-a8de-9da3d9ceda5e
-- title:
--   Lemma 2.18 — potential decrease controls the response residual
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Let the steps satisfy (13), and let $\alpha$ be a multiplier profile with $y=\bar v\alpha\in\mathcal Y$; write $\alpha^+$ for one step of the damped dynamics from $\alpha$. Then
--   $$
--   0\le\mathcal V(\alpha)\le1,\qquad \mathcal V(\alpha^+)\le\theta^2\,\mathcal V(\alpha), \tag{44}
--   $$
--   and
--   $$
--   \|\mathcal R(\alpha)\|_\infty^2\le Q_{\mathrm{res}}^2\,\mathcal V(\alpha)\le\frac{Q_{\mathrm{res}}^2}{1-\theta^2}\big(\mathcal V(\alpha)-\mathcal V(\alpha^+)\big). \tag{46}
--   $$
--
--   Differences from the source:
--   - encoding: h_i, e_i, E and p^[k] as functions → defined through a choice among conditional equilibria (condEq); reason: the conditional equilibrium is unique on 𝒴 (Lemma 2.11), so the choice is the paper's map
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.18, (44)–(46), p.23

import Mathlib
import Definitions.Def_AutobidSPPE_StepCondition
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_potential
import Definitions.Def_AutobidSPPE_residual
import Definitions.Def_AutobidSPPE_iterate
import Definitions.Def_AutobidSPPE_theta
import Definitions.Def_AutobidSPPE_Qres

namespace AutobidSPPE

/-- Lemma 2.18, p.23 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), potential decrease controls the response residual: under the step
condition (13), for `α` with `y = v̄α ∈ 𝒴` and `α⁺` the damped update, `0 ≤ 𝒱(α) ≤ 1` and
`𝒱(α⁺) ≤ θ²𝒱(α)` (44), and `‖𝓡(α)‖²_∞ ≤ Q_res²𝒱(α) ≤ Q_res²/(1 − θ²)·(𝒱(α) − 𝒱(α⁺))` (46).

**Formalization Note** `α⁺` is one step of the dynamics, `iterate … α 1`. -/
theorem lemma_2_18 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (τ : Fin n → ℝ) (hτ : StepCondition vhat ρ τ) (tie : TieRule n) :
    ∀ α : Fin n → ℝ, (fun i => vbar i * α i) ∈ endpointBox vbar ρ →
      0 ≤ potential vbar vhat ρ α ∧ potential vbar vhat ρ α ≤ 1 ∧
      potential vbar vhat ρ (iterate vbar ρ tie τ α 1) ≤
        theta vhat ρ τ ^ 2 * potential vbar vhat ρ α ∧
      ‖residual vbar ρ tie α‖ ^ 2 ≤ Qres vhat ρ ^ 2 * potential vbar vhat ρ α ∧
      Qres vhat ρ ^ 2 * potential vbar vhat ρ α ≤
        Qres vhat ρ ^ 2 / (1 - theta vhat ρ τ ^ 2) *
          (potential vbar vhat ρ α - potential vbar vhat ρ (iterate vbar ρ tie τ α 1)) := by sorry

end AutobidSPPE
