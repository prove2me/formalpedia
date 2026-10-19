-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_6
-- name    : DriftVarCtrl.FixedLB.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:16.101928+00:00
-- url     : https://prove2.me/theorems/be2e70a3-95a1-4c1d-9d3e-8310a0dcf911
-- title:
--   Lemma 6, p. EC-11 — ∂f₁/∂S > 0 and ∂f₁/∂h₂ < 0 on the (9)-interval
-- statement:
--   Assume $v_1 < v_2$. Let $S \in [0,U]$ and $h_2 \in (d_2^L\Delta h_1 + h_2^*,\ d_1^U\Delta h_1 + h_2^*)$. Then
--   $$\frac{\partial f_1}{\partial S}(S,h_2) > 0,\qquad \frac{\partial f_1}{\partial h_2}(S,h_2) < 0 .$$
--
--   Monotonicity of $f_1$ in $S$ gives uniqueness of the switching point $S^*$, and Lemmas 5–7 together give its existence by the intermediate value theorem.
--
--   **Formalization Note.** The partial derivatives are derivatives of the one-variable sections $S \mapsto f_1(S,h_2)$ and $h \mapsto f_1(S,h)$. The page writes "$d^U_I$" for $d_1^U$ and assumes "$h_1 > 0$", which is part of the model; when $\Delta h_1 \le 0$ the $h_2$-interval is empty (by Lemma 1), so the statement is as printed. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-11, Lemma 6

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 6 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-11). Fix `h₁ > 0`, let `S ∈ [0, U]` and
`h₂ ∈ (dᴸ₂Δh₁ + h*₂, dᵁ₁Δh₁ + h*₂)`. Then `∂f₁/∂S > 0` and `∂f₁/∂h₂ < 0`.

Formalization Note: the partial derivatives are `deriv` of the one-variable sections
`S ↦ f₁(S, h₂)` and `h ↦ f₁(S, h)`. The page writes `dᵁᴵ` for `dᵁ₁`. For `Δh₁ ≤ 0` the `h₂`-interval is
empty (Lemma 1), as printed. The standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_6 (p : Params) (hv : v p .one < v p .two) (S : ℝ) (hS : S ∈ Set.Icc 0 p.U) (h₂' : ℝ)
    (h₂mem : h₂' ∈ Set.Ioo (dL2 p * Δh p .one + hstar p .two) (dU1 p * Δh p .one + hstar p .two)) :
    0 < deriv (fun S' => f1 p S' h₂') S ∧ deriv (fun h => f1 p S h) h₂' < 0 := by sorry

end DriftVarCtrl.FixedLB
