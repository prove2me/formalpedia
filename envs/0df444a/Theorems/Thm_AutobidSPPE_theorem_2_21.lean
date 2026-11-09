-- Prove2me | Theorems.Thm_AutobidSPPE_theorem_2_21
-- name    : AutobidSPPE.theorem_2_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:11:42.120219+00:00
-- url     : https://prove2.me/theorems/1d7116c8-17a3-4928-a780-48b086394739
-- title:
--   Theorem 2.21 — second stage: linear last-iterate convergence
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Let the steps satisfy (13) and let $\alpha^*$ be the Bayesian SPPE. Every initialization $\alpha^{(0)}\in[0,1]^n$ satisfies, for all $t\ge T_0$,
--   $$
--   \|\alpha^{(t)}-\alpha^*\|_\infty\le P_{\mathrm{err}}\,\theta^{t-T_0}, \tag{49}
--   $$
--   $$
--   \|\mathcal R(\alpha^{(t)})\|_\infty\le Q_{\mathrm{res}}\,\theta^{t-T_0}. \tag{50}
--   $$
--   The conclusion covers equilibria with strictly slack or weakly binding capped bidders as well as interior ones.
--
--   Differences from the source:
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 2.21, (49)–(50), p.24

import Mathlib
import Definitions.Def_AutobidSPPE_StepCondition
import Definitions.Def_AutobidSPPE_IsBayesianSPPE
import Definitions.Def_AutobidSPPE_residual
import Definitions.Def_AutobidSPPE_iterate
import Definitions.Def_AutobidSPPE_T0
import Definitions.Def_AutobidSPPE_theta
import Definitions.Def_AutobidSPPE_Perr
import Definitions.Def_AutobidSPPE_Qres

namespace AutobidSPPE

/-- Theorem 2.21, p.24 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), second stage: under the hypotheses and steps of Theorem 2.19,
every initialization in `[0,1]ⁿ` satisfies, for all `t ≥ T₀`,
`‖α⁽ᵗ⁾ − α*‖_∞ ≤ P_err θ^{t−T₀}` (49) and `‖𝓡(α⁽ᵗ⁾)‖_∞ ≤ Q_res θ^{t−T₀}` (50). -/
theorem theorem_2_21 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) (τ : Fin n → ℝ) (hτ : StepCondition vhat ρ τ) :
    ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ αstar : Fin n → ℝ, IsBayesianSPPE vbar ρ tie αstar → ∀ t : ℕ, T0 τ ≤ t →
        ‖iterate vbar ρ tie τ α0 t - αstar‖ ≤ Perr vhat ρ * theta vhat ρ τ ^ (t - T0 τ) ∧
        ‖residual vbar ρ tie (iterate vbar ρ tie τ α0 t)‖ ≤
          Qres vhat ρ * theta vhat ρ τ ^ (t - T0 τ) := by sorry

end AutobidSPPE
