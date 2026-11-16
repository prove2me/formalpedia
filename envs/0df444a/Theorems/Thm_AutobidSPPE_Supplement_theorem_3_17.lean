-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_17
-- name    : AutobidSPPE.Supplement.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:05:33.891202+00:00
-- url     : https://prove2.me/theorems/e48d93bc-eb32-4a72-b694-83928617982c
-- title:
--   Theorem 3.17 — direct contraction certificate for all fixed averaging steps
-- statement:
--   Let $n\ge3$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i$, and budgets $\rho_i>0$. Suppose $\Delta_i(S)\ge0$ for every bidder $i$ and every rival set $S\subseteq[n]\setminus\{i\}$, and $\Delta_i([n]\setminus\{i\})>0$ for every $i$. Set
--   $$
--   \sigma=\min_i\frac{4\Delta_i([n]\setminus\{i\})}{\bar v_i}\prod_{j\ne i}\underline\alpha_j>0,\qquad q=1-\sigma,\qquad \gamma=1-\sigma\min_i\tau_i(2\underline\alpha_i)\in(0,1).
--   $$
--   For every fixed $0<\tau_i\le1$, the iteration (51) converges from every start in $[0,1]^n$ to its unique SPTE $\alpha^*$. With $D=\max_i\log(1/\underline\alpha_i)$, for every $k\ge0$,
--   $$
--   \|\alpha^{T_0+k}-\alpha^*\|_\infty\le D\gamma^k,\qquad \|\mathcal R(\alpha^{T_0+k})\|_\infty\le(1+q)D\gamma^k,\qquad \sum_{t\ge0}\|\mathcal R(\alpha^t)\|_\infty^2\le T_0+\frac{(1+q)^2D^2}{1-\gamma^2},
--   $$
--   and the minimum of the first $N$ squared residuals is at most the last constant divided by $N$.
--
--   No hierarchy of the steps is needed under this coefficient certificate.
--
--   **Formalization Note** $\underline\alpha$ is the box (59), computed from $\hat v$ and $\rho$.
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - encoding: an infinite sum of squared residuals → a bound on every partial sum; reason: the terms are nonnegative, so the two are equivalent
--   - encoding: min over 0 ≤ t < N → some t < N; reason: the minimum of finitely many reals is attained
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.17, pp.38–39

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT
import Definitions.Def_AutobidSPPE_Supplement_slackT
import Definitions.Def_AutobidSPPE_Supplement_sigmaT
import Definitions.Def_AutobidSPPE_Supplement_qT
import Definitions.Def_AutobidSPPE_Supplement_gammaT
import Definitions.Def_AutobidSPPE_Supplement_DT
import Definitions.Def_AutobidSPPE_T0

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.17, pp.38–39 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), direct contraction certificate for all fixed averaging steps. Let `n ≥ 3`,
`vᵢ ∼ Unif[0, v̄ᵢ]` independently with `0 < v̄ᵢ ≤ v̂ᵢ`, and `ρᵢ > 0`. Suppose `Δᵢ(S) ≥ 0` for every bidder `i` and
every rival set `S ⊆ [n]∖{i}`, and `Δᵢ([n]∖{i}) > 0` for every `i`. Then `σ > 0`, and for every fixed
`0 < τᵢ ≤ 1`: `γ = 1 − σ minᵢ τᵢ(2α̲ᵢ) ∈ (0,1)`; the iteration (51) has a unique SPTE `α*` and converges to it from
every start in `[0,1]ⁿ`; with `q = 1 − σ` and `D = maxᵢ log(1/α̲ᵢ)`, for every `k ≥ 0`,
`‖α^{T₀+k} − α*‖_∞ ≤ Dγᵏ`, `‖R(α^{T₀+k})‖_∞ ≤ (1 + q)Dγᵏ`, and
`Σ_{t≥0} ‖R(αᵗ)‖²_∞ ≤ T₀ + (1 + q)²D²/(1 − γ²)`; in particular the minimum of the first `N` squared residuals
is at most that constant divided by `N`.

**Formalization Note** `α̲` is the box (59), built from `v̂` and `ρ`. The infinite sum is a bound on every partial
sum; "minimum of the first `N`" is "some `t < N`". `‖·‖` is the sup norm. Every tie rule is allowed. -/
theorem theorem_3_17 {n : ℕ} (hn : 3 ≤ n) (vbar vhat ρ : Fin n → ℝ)
    (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i) (hρ : ∀ i, 0 < ρ i) (tie : TieRule n)
    (hslack : ∀ i, ∀ S ⊆ Finset.univ.erase i, 0 ≤ slackT vbar i S)
    (hfull : ∀ i, 0 < slackT vbar i (Finset.univ.erase i)) :
    0 < sigmaT vbar vhat ρ ∧
    ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) →
      0 < gammaT vbar vhat ρ τ ∧ gammaT vbar vhat ρ τ < 1 ∧
      ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
        (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
        ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
          Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds αstar) ∧
          (∀ k : ℕ,
            ‖iterateT vbar ρ tie τ α0 (T0 τ + k) - αstar‖ ≤ DT vhat ρ * gammaT vbar vhat ρ τ ^ k ∧
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 (T0 τ + k))‖ ≤
              (1 + qT vbar vhat ρ) * DT vhat ρ * gammaT vbar vhat ρ τ ^ k) ∧
          (∀ N : ℕ, ∑ t ∈ Finset.range N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤
              (T0 τ : ℝ) + (1 + qT vbar vhat ρ) ^ 2 * DT vhat ρ ^ 2 / (1 - gammaT vbar vhat ρ τ ^ 2)) ∧
          ∀ N : ℕ, 1 ≤ N → ∃ t < N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤
              ((T0 τ : ℝ) + (1 + qT vbar vhat ρ) ^ 2 * DT vhat ρ ^ 2 /
                (1 - gammaT vbar vhat ρ τ ^ 2)) / N := by sorry

end AutobidSPPE.Supplement
