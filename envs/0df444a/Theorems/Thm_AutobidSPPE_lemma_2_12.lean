-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_12
-- name    : AutobidSPPE.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:02:21.860284+00:00
-- url     : https://prove2.me/theorems/170f8d15-0508-44a5-aee3-920597bb58e2
-- title:
--   Lemma 2.12 — spending and response bounds
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$.
--
--   1. For $a>0$ and positive rival endpoints $w$,
--   $$
--   0<\partial_a\mathsf s_i(a,w)\le1,\qquad \partial_a\mathsf s_i(a,w)\ge\frac{\mathsf s_i(a,w)^2}{a^2}. \tag{30}
--   $$
--   2. Spending is $1$-Lipschitz in the rival endpoints (for $a>0$ and positive rivals) and $2$-Lipschitz in all endpoint coordinates on $(0,\infty)^n$.
--   3. Consequently, on $(0,\infty)^n$ the Jacobian satisfies
--   $$
--   |(J_s)_{ij}|\le1,\qquad \|J_s\|_\infty\le2 \tag{31}
--   $$
--   (maximum absolute row sum).
--   4. The capped endpoint response $\mathsf b_i$ is $U^2/\rho_i^2$-Lipschitz in its rivals on positive rival endpoints, and the full endpoint response map is $L_r$-Lipschitz on $\mathcal Y$.
--
--   **Formalization Note** $\partial_a$ is the derivative of $a\mapsto\mathsf s_i(a,w)$; Lipschitz bounds in the rivals use the maximum over rival coordinates $j\ne i$.
--
--   Differences from the source:
--   - generalization: 𝖻ᵢ is U²/ρᵢ²-Lipschitz in its rivals on their positive endpoint rectangle → for all rival endpoints w, w' with positive coordinates (no upper bound v̄ⱼ); reason: the bound uses only the own endpoint ≤ v̄ᵢ ≤ U; it specializes to the rectangle ∏_{j≠i}(0, v̄ⱼ]
--   - encoding: ∂ₐ𝗌ᵢ(a, w) → deriv of a ↦ 𝗌ᵢ(a, w); reason: the ordinary derivative; the clause 0 < ∂ₐ𝗌ᵢ forces differentiability
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
--   - reading: spending is 2-Lipschitz in all endpoint coordinates and (31) holds (domain not repeated in the sentence) → both stated on the positive orthant (all endpoints > 0); reason: the lemma opens with "For a > 0 and positive rival endpoints w" and the proof derives (31) from differentiability on the positive orthant; endpoint spending is continuous up to the boundary, so the Lipschitz bound extends to the closed orthant by continuity
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.12, (30)–(31), p.17

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_endpointResponse
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_spendJac
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_Lr

namespace AutobidSPPE

/-- Lemma 2.12, p.17 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): for `a > 0` and positive rival endpoints `w`,
`0 < ∂ₐ𝗌ᵢ(a, w) ≤ 1` and `∂ₐ𝗌ᵢ(a, w) ≥ 𝗌ᵢ(a, w)²/a²` (30); spending is `1`-Lipschitz in the
rival endpoints and `2`-Lipschitz in all endpoint coordinates; `|(J_s)ᵢⱼ| ≤ 1` and
`‖J_s‖_∞ ≤ 2` (31); the capped endpoint response `𝖻ᵢ` is `U²/ρᵢ²`-Lipschitz in its rivals on their
positive endpoint rectangle; and the full endpoint response map is `L_r`-Lipschitz on `𝒴`.

**Formalization Note** `∂ₐ` is `deriv` of `a ↦ 𝗌ᵢ(a, w)`; Lipschitz bounds use sup norms (over the
rival indices `j ≠ i` where stated); `‖J_s‖_∞` is the maximum absolute row sum; `J_s` is evaluated
on the positive orthant; the response bound is stated for all positive rival endpoints. -/
theorem lemma_2_12 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i) :
    (∀ (i : Fin n) (a : ℝ) (w : Fin n → ℝ), 0 < a → (∀ j, j ≠ i → 0 < w j) →
      0 < deriv (fun b => endpointSpend (Function.update w i b) i) a ∧
      deriv (fun b => endpointSpend (Function.update w i b) i) a ≤ 1 ∧
      endpointSpend (Function.update w i a) i ^ 2 / a ^ 2 ≤
        deriv (fun b => endpointSpend (Function.update w i b) i) a) ∧
    (∀ (i : Fin n) (a : ℝ) (w w' : Fin n → ℝ), 0 < a → (∀ j, j ≠ i → 0 < w j) →
      (∀ j, j ≠ i → 0 < w' j) →
      |endpointSpend (Function.update w i a) i - endpointSpend (Function.update w' i a) i| ≤
        ‖fun j : {j : Fin n // j ≠ i} => w j - w' j‖) ∧
    (∀ y y' : Fin n → ℝ, (∀ j, 0 < y j) → (∀ j, 0 < y' j) → ∀ i,
      |endpointSpend y i - endpointSpend y' i| ≤ 2 * ‖y - y'‖) ∧
    (∀ y : Fin n → ℝ, (∀ j, 0 < y j) →
      (∀ i j, |spendJac y i j| ≤ 1) ∧ ∀ i, ∑ j, |spendJac y i j| ≤ 2) ∧
    (∀ (i : Fin n) (w w' : Fin n → ℝ), (∀ j, j ≠ i → 0 < w j) → (∀ j, j ≠ i → 0 < w' j) →
      |endpointResponse vbar ρ w i - endpointResponse vbar ρ w' i| ≤
        supU vhat ^ 2 / ρ i ^ 2 * ‖fun j : {j : Fin n // j ≠ i} => w j - w' j‖) ∧
    (∀ y ∈ endpointBox vbar ρ, ∀ z ∈ endpointBox vbar ρ,
      ‖(fun i => endpointResponse vbar ρ y i) - (fun i => endpointResponse vbar ρ z i)‖ ≤
        Lr vhat ρ * ‖y - z‖) := by sorry

end AutobidSPPE
