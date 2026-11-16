-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_1
-- name    : AutobidSPPE.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:01:50.831258+00:00
-- url     : https://prove2.me/theorems/1c292bc0-f207-48d7-846d-92daeece190a
-- title:
--   Theorem 3.1 — uniform SPTE convergence: proved regimes
-- statement:
--   Let $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $\bar v_i>0$, and budgets $\rho_i>0$. Consider the Bayesian second-price throttling equilibrium (SPTE) and the simultaneous averaged exact-response iteration $\alpha^{(t+1)}_i=(1-\tau_i)\alpha^{(t)}_i+\tau_i r_i(\alpha^{(t)}_{-i})$ from any $\alpha^{(0)}\in[0,1]^n$, with residual $\mathcal R=\alpha-r(\alpha)$ and the max norm.
--
--   1. **Two bidders.** If $n=2$ and $0<\tau_i\le1$, $\tau_1+\tau_2\le1$, every trajectory converges to an SPTE $\alpha^\infty$, its squared residuals have bounded partial sums, and there are $T$, $C$ and $q\in(0,1)$ with $\|\alpha^{(t)}-\alpha^\infty\|_\infty\le Cq^{t-T}$ for $t\ge T$. The SPTE need not be unique: some two-bidder instance with positive supports and budgets has two distinct SPTEs.
--   2. **Three bidders.** If $n=3$, the SPTE $\alpha^*$ is unique. For every certified upper bound $\hat v\ge\bar v$ and steps satisfying (63) with $m$ from (61) and the constants (59), (62), (80), every trajectory converges to $\alpha^*$ and
--   $$
--   \sum_{t\ge0}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le C_{\mathrm{res}},\qquad \min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le\frac{C_{\mathrm{res}}}{N},
--   $$
--   $$
--   \|\alpha^{(T_0+k)}-\alpha^*\|_\infty\le P_{\mathrm{err}}\theta^k,\qquad \|\mathcal R(\alpha^{(T_0+k)})\|_\infty\le Q_{\mathrm{res}}\theta^k\quad(k\ge0).
--   $$
--   3. **Support spread.** If $n\ge3$ and, with $A=\min_i\bar v_i$ and $\eta=\max_i\bar v_i/A-1$,
--   $$
--   \eta<\frac{1}{(2n-1)n(n+1)},
--   $$
--   the SPTE $\alpha^*$ is unique and, for every fixed $0<\tau_i\le1$, convergence is globally geometric: there are $C$ and $q\in(0,1)$ with $\|\alpha^{(t)}-\alpha^*\|_\infty\le Cq^t$ for all $t$ and all starts.
--   4. **Budgets.** If $\rho_j\ge\bar v_j/4$ for all but at most one bidder, the same conclusion as in 3 holds.
--
--   In every regime there is a constant $C$, independent of the start, with $\min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le C/N$ for every $N\ge1$.
--
--   The theorem lists the proved convergence regimes for throttling; Theorems 3.14–3.19 supply the arguments and constants.
--
--   **Formalization Note** "Globally geometric" and the $O(1/N)$ bound are stated with constants that do not depend on the start. Summability is a bound on all partial sums. The constants in part 2 are computed from the certified bounds $\hat v$, as in (59)–(62).
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - encoding: an infinite sum of squared residuals → a bound on every partial sum; reason: the terms are nonnegative, so the two are equivalent
--   - encoding: min over 0 ≤ t < N → some t < N; reason: the minimum of finitely many reals is attained
--   - encoding: steps (63) for any fixed bidder ordering → StepCondT: there is a permutation σ of Fin n with the inequalities along σ; reason: a fixed ordering of the bidders is a permutation
--   - reading: globally geometric convergence → ∃ C, q ∈ (0,1) with ‖α^(t) − α*‖ ≤ C q^t for all t and all starts in [0,1]^n; reason: constants uniform in the start, the stronger reading, which the proofs give
--   - reading: O(1/N) bound on the squared best-iterate residual, for the same trajectory → ∃ C, uniform in the start, with min_{t<N} ‖R(α^(t))‖² ≤ C/N for every N ≥ 1; reason: the stronger reading; the proofs give constants independent of the start
--   - reading: an SPTE, which need not be unique → there is a two-bidder instance (positive supports and budgets) with two distinct SPTEs, for every tie rule; reason: 'need not be unique' is a claim that non-uniqueness occurs (the continuum xy = b of §3.14)
--   - reading: part 2: the explicit, recalculated constants below → for every certified bound v̂ ≥ v̄ and steps (63) with m = (61): the bounds (82) and (83) with the constants (59), (62), (80); reason: the constants are built from the certified bounds v̂ of A1; quantifying over every v̂ ≥ v̄ covers every admissible choice
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.1, p.25

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT
import Definitions.Def_AutobidSPPE_Supplement_StepCondT
import Definitions.Def_AutobidSPPE_Supplement_mThree
import Definitions.Def_AutobidSPPE_Supplement_CresT
import Definitions.Def_AutobidSPPE_Supplement_PerrT
import Definitions.Def_AutobidSPPE_Supplement_thetaT
import Definitions.Def_AutobidSPPE_T0

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.1, p.25 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), uniform SPTE convergence: proved regimes. Let `n ≥ 2`, `vᵢ ∼ Unif[0, v̄ᵢ]`
independently with `v̄ᵢ > 0`, and `ρᵢ > 0`. For the iteration (51) from every `α⁽⁰⁾ ∈ [0,1]ⁿ`:
1. `n = 2`, `τ₁ + τ₂ ≤ 1`: the iteration converges to an SPTE, squared residuals are summable, and the limit has
   an eventual geometric distance bound; the SPTE need not be unique (some two-bidder instance has two).
2. `n = 3`: the SPTE is unique; for every certified `v̂ ≥ v̄` and steps (63) with `m` from (61) and the constants
   (59), (62), (80), the bounds (82) and (83) hold.
3. `n ≥ 3` and `η = maxᵢ v̄ᵢ / minᵢ v̄ᵢ − 1 < 1/((2n−1)n(n+1))` (52): the SPTE is unique and convergence is globally
   geometric for every fixed `0 < τᵢ ≤ 1`.
4. `ρⱼ ≥ v̄ⱼ/4` for all but at most one bidder: the same as 3.
Every regime gives an `O(1/N)` bound on the squared best-iterate residual.

**Formalization Note** "Globally geometric" is: there are `C` and `q ∈ (0,1)`, uniform in the start, with
`‖α⁽ᵗ⁾ − α*‖ ≤ C qᵗ` for all `t`. "`O(1/N)`" is: some `C`, uniform in the start, with
`min_{t<N} ‖R(α⁽ᵗ⁾)‖² ≤ C/N` for every `N ≥ 1` ("min over `t < N`" is "some `t < N`"). Summability is a
uniform bound on the partial sums. Norms are the sup norm. Every tie rule is allowed. -/
theorem theorem_3_1 {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i)
    (hρ : ∀ i, 0 < ρ i) (tie : TieRule n) :
    -- regime 1: two bidders, `τ₁ + τ₂ ≤ 1`
    (n = 2 → ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) → ∑ i, τ i ≤ 1 →
      (∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
        ∃ αinf : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αinf ∧
          Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds αinf) ∧
          (∃ C : ℝ, ∀ N : ℕ, ∑ t ∈ Finset.range N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ C) ∧
          ∃ (T : ℕ) (C q : ℝ), 0 < q ∧ q < 1 ∧ ∀ t : ℕ, T ≤ t →
            ‖iterateT vbar ρ tie τ α0 t - αinf‖ ≤ C * q ^ (t - T)) ∧
      ∃ C : ℝ, ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) → ∀ N : ℕ, 1 ≤ N → ∃ t < N,
        ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ C / N) ∧
    -- regime 1: "which need not be unique"
    (∃ vb ρ' : Fin 2 → ℝ, (∀ i, 0 < vb i) ∧ (∀ i, 0 < ρ' i) ∧ ∀ tie' : TieRule 2,
      ∃ α β : Fin 2 → ℝ, IsBayesianSPTE vb ρ' tie' α ∧ IsBayesianSPTE vb ρ' tie' β ∧ α ≠ β) ∧
    -- regime 2: three bidders, explicit constants
    (n = 3 → ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
      (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
      ∀ vhat : Fin n → ℝ, (∀ i, vbar i ≤ vhat i) → ∀ τ : Fin n → ℝ,
        StepCondT vhat ρ (mThree vbar vhat ρ) τ →
        ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
          Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds αstar) ∧
          (∀ N : ℕ, ∑ t ∈ Finset.range N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤
              CresT vhat ρ (mThree vbar vhat ρ) τ) ∧
          (∀ N : ℕ, 1 ≤ N → ∃ t < N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤
              CresT vhat ρ (mThree vbar vhat ρ) τ / N) ∧
          ∀ k : ℕ,
            ‖iterateT vbar ρ tie τ α0 (T0 τ + k) - αstar‖ ≤
              PerrT vhat ρ (mThree vbar vhat ρ) * thetaT vhat (mThree vbar vhat ρ) τ ^ k ∧
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 (T0 τ + k))‖ ≤
              QresT vhat ρ (mThree vbar vhat ρ) * thetaT vhat (mThree vbar vhat ρ) τ ^ k) ∧
    -- regime 3: support spread (52)
    (3 ≤ n → (⨆ i, vbar i) / (⨅ i, vbar i) - 1 < 1 / ((2 * (n : ℝ) - 1) * n * (n + 1)) →
      ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
        (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
        ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) →
          (∃ C q : ℝ, 0 < q ∧ q < 1 ∧ ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
            ∀ t : ℕ, ‖iterateT vbar ρ tie τ α0 t - αstar‖ ≤ C * q ^ t) ∧
          ∃ C : ℝ, ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) → ∀ N : ℕ, 1 ≤ N → ∃ t < N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ C / N) ∧
    -- regime 4: `ρⱼ ≥ v̄ⱼ/4` for all but at most one bidder
    ((∃ i, ∀ j, j ≠ i → vbar j / 4 ≤ ρ j) →
      ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
        (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
        ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) →
          (∃ C q : ℝ, 0 < q ∧ q < 1 ∧ ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
            ∀ t : ℕ, ‖iterateT vbar ρ tie τ α0 t - αstar‖ ≤ C * q ^ t) ∧
          ∃ C : ℝ, ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) → ∀ N : ℕ, 1 ≤ N → ∃ t < N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ C / N) := by sorry

end AutobidSPPE.Supplement
