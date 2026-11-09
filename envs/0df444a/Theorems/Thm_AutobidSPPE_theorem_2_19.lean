-- Prove2me | Theorems.Thm_AutobidSPPE_theorem_2_19
-- name    : AutobidSPPE.theorem_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:11:39.635199+00:00
-- url     : https://prove2.me/theorems/18088c95-3341-493f-b2f2-a54dca9d72aa
-- title:
--   Theorem 2.19 — first stage: squared best-iterate residual
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Let the steps satisfy (13). Every initialization $\alpha^{(0)}\in[0,1]^n$ of the damped dynamics satisfies
--   $$
--   \min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le\frac{C_{\mathrm{res}}}{N}\quad(N\ge1),\qquad C_{\mathrm{res}}=T_0+\frac{Q_{\mathrm{res}}^2}{1-\theta^2}. \tag{47}
--   $$
--   Moreover, the squared residuals $\|\mathcal R(\alpha^{(t)})\|_\infty^2$ are summable over $t$, and the trajectory converges to the unique Bayesian SPPE.
--
--   Differences from the source:
--   - encoding: min_{0≤t<N} a_t ≤ c → ∃ t < N, a_t ≤ c; reason: equivalent for a finite nonempty range
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 2.19, (47), p.23

import Mathlib
import Definitions.Def_AutobidSPPE_StepCondition
import Definitions.Def_AutobidSPPE_IsBayesianSPPE
import Definitions.Def_AutobidSPPE_residual
import Definitions.Def_AutobidSPPE_iterate
import Definitions.Def_AutobidSPPE_Cres

namespace AutobidSPPE

/-- Theorem 2.19, p.23 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), first stage: under the uniform model and the step condition (13),
every initialization `α⁽⁰⁾ ∈ [0,1]ⁿ` satisfies `min_{0≤t<N} ‖𝓡(α⁽ᵗ⁾)‖²_∞ ≤ C_res/N` for `N ≥ 1`
(47); the squared residuals are summable; and the trajectory converges to the unique SPPE.

**Formalization Note** "`min_{0≤t<N} … ≤ C_res/N`" is written as "some `t < N` has
`… ≤ C_res/N`", which is equivalent. -/
theorem theorem_2_19 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) (τ : Fin n → ℝ) (hτ : StepCondition vhat ρ τ) :
    ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ N : ℕ, 1 ≤ N → ∃ t < N,
        ‖residual vbar ρ tie (iterate vbar ρ tie τ α0 t)‖ ^ 2 ≤ Cres vhat ρ τ / N) ∧
      Summable (fun t => ‖residual vbar ρ tie (iterate vbar ρ tie τ α0 t)‖ ^ 2) ∧
      ∃ αstar : Fin n → ℝ, IsBayesianSPPE vbar ρ tie αstar ∧
        (∀ β, IsBayesianSPPE vbar ρ tie β → β = αstar) ∧
        Filter.Tendsto (iterate vbar ρ tie τ α0) Filter.atTop (nhds αstar) := by sorry

end AutobidSPPE
