-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_3
-- name    : ContextualAuctions.Existence.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:47.294983+00:00
-- url     : https://prove2.me/theorems/a5041fe1-0fb2-4437-8d5b-c8e475ab5e3d
-- title:
--   Lemma 3, p. 10 — ℓ^µ ∈ L₁(Θ) and V(ℓ^µ, Θ) ≤ V₀ = (d+1)max(U^d,U^{d+1})ω/B_min (printed constant (d+1)U^{d+1}ω/B_min corrected for U < 1)
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions. For any pacing function $\mu:\Theta\to[0,\omega/B_{\min}]$:
--
--   1. $\ell^\mu\in L_1(\Theta)$, i.e. $\ell^\mu$ is Lebesgue integrable on $\Theta$;
--   2. its total variation on $\Theta\subset\mathbb R^{d+1}$ satisfies
--   $$
--   V(\ell^\mu,\Theta)\le V_0:=\frac{(d+1)\,\max(U^{d},U^{d+1})\,\omega}{B_{\min}} .
--   $$
--
--   Together with $0\le\ell^\mu\le\omega/B_{\min}$ this says $\ell^\mu\in\mathcal X_0$, so the correspondence $C^*_0$ of the fixed-point argument always has a candidate in the compact set $\mathcal X_0$.
--
--   **Formalization Note** Integrability is with respect to Lebesgue measure on $\Theta$, not $G$; part 1 includes measurability of $\ell^\mu$. $V$ is valued in the extended reals. The pacing function is assumed measurable. **Constant:** the paper prints $V_0=(d+1)U^{d+1}\omega/B_{\min}$, and the statement above is exactly that when $U\ge1$. For $U<1$ the printed bound is false. Rescaling $(w,B,U,B_{\min},r)$ by $s$ leaves $\ell^\mu$ and $\omega/B_{\min}$ unchanged, scales $V(\ell^\mu,\Theta)$ by $s^d$ and scales $U^{d+1}$ by $s^{d+1}$. The constant is therefore corrected to $U^d$ there, which is the bound for coordinatewise monotone functions (Lemma 2) with values in $[0,\omega/B_{\min}]$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 3

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

open MeasureTheory

/-- Lemma 3. `V0` is `(d + 1) max(U^d, U^{d+1}) ω / B_min`. It equals the printed
`(d + 1) U^{d+1} ω / B_min` when `U ≥ 1`; for `U < 1` the printed bound is false (see `V0`). -/
theorem lemma_3 (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    IntegrableOn (ell M μ) (Theta M) ∧ Vtheta M (ell M μ) ≤ (V0 M : EReal) := by sorry

end ContextualAuctions.Existence
