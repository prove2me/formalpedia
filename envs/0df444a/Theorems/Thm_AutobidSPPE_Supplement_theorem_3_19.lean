-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_19
-- name    : AutobidSPPE.Supplement.theorem_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:07:19.374349+00:00
-- url     : https://prove2.me/theorems/03acf59b-be4c-4ab0-8aca-b7372ae66fce
-- title:
--   Theorem 3.19 — a complete two-bidder replacement
-- statement:
--   Let two bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $\bar v_i>0$, budgets $\rho_i>0$, and fixed steps $\tau_i>0$ with $\tau_1+\tau_2\le1$. Every trajectory of (51) from $[0,1]^2$ converges to an SPTE $\alpha^\infty$, and
--   $$
--   \sum_{t\ge0}\|\mathcal R(\alpha^{(t)})\|_2^2\le3(\tau_1^{-1}+\tau_2^{-1}),\qquad \min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le\frac{3(\tau_1^{-1}+\tau_2^{-1})}{N}.
--   $$
--   There exist finite $T$, $C_2$ and $q\in(0,1)$ with $\|\alpha^{(t)}-\alpha^\infty\|_2\le C_2q^{t-T}$ for $t\ge T$. With $v_0=\min\{\bar v_1,\bar v_2\}$,
--   $$
--   \beta_1=\frac{v_0^2}{2\bar v_2}-\frac{v_0^3}{3\bar v_1\bar v_2},\qquad \beta_2=\frac{v_0^2}{2\bar v_1}-\frac{v_0^3}{3\bar v_1\bar v_2},
--   $$
--   and $b_i=\rho_i/\beta_i$, the limit can depend on the initialization when $b_1=b_2<1$: there are two starts whose limits differ.
--
--   For two bidders the spending Jacobian is singular and the SPTE need not be unique; this theorem replaces the uniqueness-based argument.
--
--   **Formalization Note** $\|x\|_2^2=\sum_ix_i^2$ and $\|x\|_2$ is its square root; the minimum uses the max norm.
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - encoding: an infinite sum of squared residuals → a bound on every partial sum; reason: the terms are nonnegative, so the two are equivalent
--   - encoding: min over 0 ≤ t < N → some t < N; reason: the minimum of finitely many reals is attained
--   - encoding: bidders 1, 2 → 0, 1 : Fin 2; reason: Lean indexing
--   - reading: The limit can depend on the initialization when b1 = b2 < 1 → if b1 = b2 < 1, there are two starts in [0,1]² whose trajectories converge to different limits; reason: 'can depend' asserts that dependence occurs
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.19, p.41; (84), p.41

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.19, p.41 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), a complete two-bidder replacement. Let `n = 2`, `vᵢ ∼ Unif[0, v̄ᵢ]` independently
with `v̄ᵢ > 0`, `ρᵢ > 0`, and fixed steps `τᵢ > 0` with `τ₁ + τ₂ ≤ 1`. Every trajectory of (51) from `[0,1]²`
converges to an SPTE `α^∞`, with
`Σ_{t≥0} ‖R(α⁽ᵗ⁾)‖²₂ ≤ 3(τ₁⁻¹ + τ₂⁻¹)` and `min_{0≤t<N} ‖R(α⁽ᵗ⁾)‖²_∞ ≤ 3(τ₁⁻¹ + τ₂⁻¹)/N` (85), and there exist
finite `T`, `C₂` and `q ∈ (0,1)` with `‖α⁽ᵗ⁾ − α^∞‖₂ ≤ C₂ q^{t−T}` for `t ≥ T`. With `v₀ = min{v̄₁, v̄₂}`,
`β₁ = v₀²/(2v̄₂) − v₀³/(3v̄₁v̄₂)`, `β₂ = v₀²/(2v̄₁) − v₀³/(3v̄₁v̄₂)` (84) and `bᵢ = ρᵢ/βᵢ`, the limit can depend on the
initialization when `b₁ = b₂ < 1`: there are two starts whose limits differ.

**Formalization Note** Bidders 1, 2 are `0, 1 : Fin 2`. `‖x‖²₂` is `Σᵢ xᵢ²` and `‖x‖₂` is its square root;
`‖·‖` (in the minimum) is the sup norm. The infinite sum is a bound on every partial sum; "min over
`0 ≤ t < N`" is "some `t < N`". Every tie rule is allowed. -/
theorem theorem_3_19 (vbar ρ : Fin 2 → ℝ) (hvbar : ∀ i, 0 < vbar i) (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule 2) (τ : Fin 2 → ℝ) (hτ : ∀ i, 0 < τ i) (hτsum : τ 0 + τ 1 ≤ 1) :
    (∀ α0 : Fin 2 → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
      ∃ αinf : Fin 2 → ℝ, IsBayesianSPTE vbar ρ tie αinf ∧
        Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds αinf) ∧
        (∀ N : ℕ, ∑ t ∈ Finset.range N,
          ∑ i, (residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t) i) ^ 2 ≤ 3 * (1 / τ 0 + 1 / τ 1)) ∧
        (∀ N : ℕ, 1 ≤ N → ∃ t < N,
          ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ 3 * (1 / τ 0 + 1 / τ 1) / N) ∧
        ∃ (T : ℕ) (C₂ q : ℝ), 0 < q ∧ q < 1 ∧ ∀ t : ℕ, T ≤ t →
          Real.sqrt (∑ i, (iterateT vbar ρ tie τ α0 t i - αinf i) ^ 2) ≤ C₂ * q ^ (t - T)) ∧
    (let v0 : ℝ := min (vbar 0) (vbar 1)
     let β : Fin 2 → ℝ := fun i =>
       if i = 0 then v0 ^ 2 / (2 * vbar 1) - v0 ^ 3 / (3 * vbar 0 * vbar 1)
       else v0 ^ 2 / (2 * vbar 0) - v0 ^ 3 / (3 * vbar 0 * vbar 1)
     ρ 0 / β 0 = ρ 1 / β 1 → ρ 0 / β 0 < 1 →
       ∃ α0 α0' L L' : Fin 2 → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, α0' i ∈ Set.Icc (0 : ℝ) 1) ∧
         Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds L) ∧
         Filter.Tendsto (iterateT vbar ρ tie τ α0') Filter.atTop (nhds L') ∧ L ≠ L') := by sorry

end AutobidSPPE.Supplement
