-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_10
-- name    : AutobidSPPE.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:31.991386+00:00
-- url     : https://prove2.me/theorems/3be1d1ee-9411-4923-a371-5e4922a357fe
-- title:
--   Lemma 2.10 — a strong P-function modulus on the actual box
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i$, and budgets $\rho_i>0$. There is $\mu_P>0$ such that
--   $$
--   \max_i\,(y_i-w_i)\big(\mathsf s_i(y)-\mathsf s_i(w)\big)\ \ge\ \mu_P\,\|y-w\|_\infty^2\qquad(y,w\in\mathcal Y). \tag{29}
--   $$
--
--   The modulus is instance-dependent; it is used for uniqueness and Lipschitz continuity of conditional equilibria, not for choosing steps.
--
--   Differences from the source:
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: max_i over bidders → ⨆ i over Fin n; reason: a finite nonempty index set (n ≥ 2), so the real supremum is the maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.10, (29), p.16

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_endpointBox

namespace AutobidSPPE

/-- Lemma 2.10, p.16 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): for the fixed actual instance there is `μ_P > 0` with
`maxᵢ (yᵢ − wᵢ)(𝗌ᵢ(y) − 𝗌ᵢ(w)) ≥ μ_P ‖y − w‖²_∞` for all `y, w ∈ 𝒴` (29).

**Formalization Note** `‖·‖` on `Fin n → ℝ` is the sup norm; the maximum over `Fin n` is `⨆ i`. -/
theorem lemma_2_10 {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i) (hρ : ∀ i, 0 < ρ i) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ endpointBox vbar ρ, ∀ w ∈ endpointBox vbar ρ,
      μ * ‖y - w‖ ^ 2 ≤ ⨆ i, (y i - w i) * (endpointSpend y i - endpointSpend w i) := by sorry

end AutobidSPPE
