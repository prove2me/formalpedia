-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_17
-- name    : AutobidSPPE.lemma_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:11:42.617841+00:00
-- url     : https://prove2.me/theorems/daf5df3d-34b3-4194-9173-c0c4fb60506b
-- title:
--   Lemma 2.17 — one-step contraction of triangular errors
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Let the steps satisfy (13). For the simultaneous update $y^+_i=y_i-\tau_i\mathcal G_i(y)$ from $y\in\mathcal Y$,
--   $$
--   E(y^+)\le\theta\,E(y),\qquad \theta=1-\frac{a\,\tau_{\min}}{2}\in(0,1),\qquad \tau_{\min}=\min_i\tau_i . \tag{41}
--   $$
--
--   This is the one-step contraction behind both convergence stages.
--
--   Differences from the source:
--   - encoding: h_i, e_i, E and p^[k] as functions → defined through a choice among conditional equilibria (condEq); reason: the conditional equilibrium is unique on 𝒴 (Lemma 2.11), so the choice is the paper's map
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.17, (41), p.22

import Mathlib
import Definitions.Def_AutobidSPPE_StepCondition
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_endpointResidual
import Definitions.Def_AutobidSPPE_weightedError
import Definitions.Def_AutobidSPPE_theta

namespace AutobidSPPE

/-- Lemma 2.17, p.22 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), one-step contraction of triangular errors: under the step
condition (13), for the simultaneous update `y⁺ᵢ = yᵢ − τᵢ𝒢ᵢ(y)` on `𝒴`,
`E(y⁺) ≤ θE(y)` with `θ = 1 − aτ_min/2 ∈ (0, 1)` (41). -/
theorem lemma_2_17 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (τ : Fin n → ℝ) (hτ : StepCondition vhat ρ τ) :
    0 < theta vhat ρ τ ∧ theta vhat ρ τ < 1 ∧
    ∀ y ∈ endpointBox vbar ρ,
      weightedError vbar vhat ρ (fun i => y i - τ i * endpointResidual vbar ρ y i) ≤
        theta vhat ρ τ * weightedError vbar vhat ρ y := by sorry

end AutobidSPPE
