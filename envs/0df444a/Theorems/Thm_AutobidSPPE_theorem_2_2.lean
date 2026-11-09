-- Prove2me | Theorems.Thm_AutobidSPPE_theorem_2_2
-- name    : AutobidSPPE.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:12:23.205545+00:00
-- url     : https://prove2.me/theorems/31a07757-4e47-4cf5-8d3c-11877a010531
-- title:
--   Theorem 2.2 — damped best responses converge linearly to the unique Bayesian SPPE
-- statement:
--   Let $n\ge2$, let $v_i\sim\mathrm{Unif}[0,\bar v_i]$ independently, and let $0<\bar v_i\le\hat v_i<\infty$ and $\rho_i>0$ for every bidder. Consider the simultaneous damped best-response dynamics with exact responses (Assumption 2.4) and fixed steps satisfying (13) (Assumption 2.5), and the constants of (10)–(12) computed from $\hat v$ and $\rho$. Set
--   $$
--   T_0=\Big\lceil\frac{\log2}{\tau_{\min}}\Big\rceil,\qquad \theta=1-\frac{a\,\tau_{\min}}{2}\in(0,1).
--   $$
--   Then the Bayesian SPPE $\alpha^*$ exists and is unique, and for every $\alpha^{(0)}\in[0,1]^n$:
--
--   1. the iteration converges to $\alpha^*$;
--   2. for every integer $N\ge1$,
--   $$
--   \min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le\frac{T_0+Q_{\mathrm{res}}^2/(1-\theta^2)}{N}; \tag{3}
--   $$
--   3. for every integer $k\ge0$,
--   $$
--   \|\alpha^{(T_0+k)}-\alpha^*\|_\infty\le P_{\mathrm{err}}\,\theta^k,\qquad \|\mathcal R(\alpha^{(T_0+k)})\|_\infty\le Q_{\mathrm{res}}\,\theta^k. \tag{4}
--   $$
--
--   All constants depend only on $n$, the certified upper bounds $\hat v_i$, the budgets and the chosen steps; neither a positive lower bound on the supports nor knowledge of the equilibrium is needed.
--
--   **Formalization Note** Bidders are `Fin n` and the step ordering is their natural order. The true supports $\bar v$ (in the value law) and the certified bounds $\hat v$ (in the constants) are separate parameters. The statement holds for every deterministic single-winner tie rule.
--
--   Differences from the source:
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: min_{0≤t<N} a_t ≤ c → ∃ t < N, a_t ≤ c; reason: equivalent for a finite nonempty range
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 2.2, (3)–(4), pp.7–8; constants (10)–(16), pp.11–12

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

/-- Theorem 2.2, pp.7–8 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), best-iterate and last-iterate guarantees. Let `n ≥ 2`,
`vᵢ ∼ Unif[0, v̄ᵢ]` independently, `0 < v̄ᵢ ≤ v̂ᵢ` and `ρᵢ > 0`. Under exact simultaneous responses
(Assumption 2.4) and fixed steps satisfying (13) (Assumption 2.5): `θ = 1 − aτ_min/2 ∈ (0, 1)`;
the Bayesian SPPE `α*` is unique (and exists); for every `α⁽⁰⁾ ∈ [0,1]ⁿ` the iteration converges to
`α*`; for every `N ≥ 1`, `min_{0≤t<N} ‖𝓡(α⁽ᵗ⁾)‖²_∞ ≤ (T₀ + Q_res²/(1 − θ²))/N` (3); and for every
`k ≥ 0`, `‖α⁽ᵀ⁰⁺ᵏ⁾ − α*‖_∞ ≤ P_err θᵏ` and `‖𝓡(α⁽ᵀ⁰⁺ᵏ⁾)‖_∞ ≤ Q_res θᵏ` (4), with
`T₀ = ⌈log 2/τ_min⌉` and the constants of (10)–(12), (15)–(16).

**Formalization Note** Bidders are `Fin n`, and the bidder ordering of Assumption 2.5 is the
order of `Fin n`. The true supports `v̄` (in the model) and the certified bounds `v̂` (in the
constants) are separate parameters. Every deterministic single-winner tie rule is allowed. The
"min over `0 ≤ t < N`" is "some `t < N`". `‖·‖` is the sup norm on `Fin n → ℝ`. -/
theorem theorem_2_2 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) (τ : Fin n → ℝ) (hτ : StepCondition vhat ρ τ) :
    0 < theta vhat ρ τ ∧ theta vhat ρ τ < 1 ∧
    ∃ αstar : Fin n → ℝ, IsBayesianSPPE vbar ρ tie αstar ∧
      (∀ β, IsBayesianSPPE vbar ρ tie β → β = αstar) ∧
      ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
        Filter.Tendsto (iterate vbar ρ tie τ α0) Filter.atTop (nhds αstar) ∧
        (∀ N : ℕ, 1 ≤ N → ∃ t < N,
          ‖residual vbar ρ tie (iterate vbar ρ tie τ α0 t)‖ ^ 2 ≤
            ((T0 τ : ℝ) + Qres vhat ρ ^ 2 / (1 - theta vhat ρ τ ^ 2)) / N) ∧
        ∀ k : ℕ,
          ‖iterate vbar ρ tie τ α0 (T0 τ + k) - αstar‖ ≤ Perr vhat ρ * theta vhat ρ τ ^ k ∧
          ‖residual vbar ρ tie (iterate vbar ρ tie τ α0 (T0 τ + k))‖ ≤
            Qres vhat ρ * theta vhat ρ τ ^ k := by sorry

end AutobidSPPE
