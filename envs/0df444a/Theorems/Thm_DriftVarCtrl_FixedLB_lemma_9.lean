-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_9
-- name    : DriftVarCtrl.FixedLB.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:14.315999+00:00
-- url     : https://prove2.me/theorems/1ad662cf-9e2c-48aa-9181-776945f903ff
-- title:
--   Lemma 9, p. EC-13 — at a root S* of f₁, F₁(S*, x, h₂) ≥ 0 for x ∈ [S*, U]
-- statement:
--   Assume $v_1 < v_2$, $\Delta h_1 > 0$ and $h_2 \in (d_2^L\Delta h_1 + h_2^*,\ d_1^U\Delta h_1 + h_2^*)$, and let $S^* \in [0,U]$ satisfy $f_1(S^*,h_2) = 0$. Then
--   $$F_1(S^*,x,h_2) \ge 0\qquad\text{for all } x \in [S^*,U].$$
--
--   This is inequality (68): on the control-2 stretch of the "1 then 2" policy, switching to control 1 does not lower the cost.
--
--   **Formalization Note.** The page assumes only $h_2 \ge d_2^L\Delta h_1 + h_2^*$ and takes $S^*$ to be "the unique value" with $f_1(S^*,h_2) = 0$. Its proof invokes Lemma 22, which needs $h_1 > h_1^*$ and the open interval of condition (9); these are stated as hypotheses, and $S^*$ is any root in $[0,U]$. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-13, Lemma 9

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 9 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-13). If `f₁(S*, h₂) = 0`, then `F₁(S*, x, h₂) ≥ 0` for all `x ∈ [S*, U]`.

Formalization Note: the page assumes only `h₂ ≥ dᴸ₂Δh₁ + h*₂` and that `S*` is "the unique value" with
`f₁(S*, h₂) = 0`; its proof uses Lemma 22, which needs `h₁ > h*₁` and
`h₂ ∈ (dᴸ₂Δh₁ + h*₂, dᵁ₁Δh₁ + h*₂)` (condition (9)). The statement takes those hypotheses and any
`S* ∈ [0, U]` with `f₁(S*, h₂) = 0`. The standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_9 (p : Params) (hv : v p .one < v p .two) (h1 : 0 < Δh p .one) (h₂' : ℝ)
    (h₂mem : h₂' ∈ Set.Ioo (dL2 p * Δh p .one + hstar p .two) (dU1 p * Δh p .one + hstar p .two))
    (S : ℝ) (hS : S ∈ Set.Icc 0 p.U) (hroot : f1 p S h₂' = 0) :
    ∀ x ∈ Set.Icc S p.U, 0 ≤ F1 p S x h₂' := by sorry

end DriftVarCtrl.FixedLB
