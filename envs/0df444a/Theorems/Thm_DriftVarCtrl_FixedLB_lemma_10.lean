-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_10
-- name    : DriftVarCtrl.FixedLB.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:12.549262+00:00
-- url     : https://prove2.me/theorems/a7ae2b85-c6c1-49a4-9be7-6d62e43998c0
-- title:
--   Lemma 10, p. EC-14 — at a root S* of f₁, F₂(S*, x, h₂) ≥ 0 for x ∈ [0, S*]
-- statement:
--   Assume $v_1 < v_2$, $\Delta h_1 > 0$ and $h_2 \in (d_2^L\Delta h_1 + h_2^*,\ d_1^U\Delta h_1 + h_2^*)$, and let $S^* \in [0,U]$ satisfy $f_1(S^*,h_2) = 0$. Then
--   $$F_2(S^*,x,h_2) \ge 0\qquad\text{for all } x \in [0,S^*].$$
--
--   This is inequality (69): on the control-1 stretch of the "1 then 2" policy, switching to control 2 does not lower the cost.
--
--   **Formalization Note.** The page assumes only $h_2 \le d_1^U\Delta h_1 + h_2^*$ with $S^*$ "defined above", and writes $F_2(S,h_2,x)$ for $F_2(S,x,h_2)$ of (70). As in Lemma 9, the hypotheses of condition (9) are stated and $S^*$ is any root of $f_1(\cdot,h_2)$ in $[0,U]$. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-14, Lemma 10

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 10 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-14). If `f₁(S*, h₂) = 0`, then `F₂(S*, x, h₂) ≥ 0` for all `x ∈ [0, S*]`.

Formalization Note: the page assumes only `h₂ ≤ dᵁ₁Δh₁ + h*₂` with `S*` "defined above" (the root of
`f₁(·, h₂)`), and writes `F₂(S, h₂, x)` for `F₂(S, x, h₂)` of (70). As for Lemma 9, the statement takes
`h₁ > h*₁`, `h₂ ∈ (dᴸ₂Δh₁ + h*₂, dᵁ₁Δh₁ + h*₂)` and any `S* ∈ [0, U]` with `f₁(S*, h₂) = 0`. The standing
`v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_10 (p : Params) (hv : v p .one < v p .two) (h1 : 0 < Δh p .one) (h₂' : ℝ)
    (h₂mem : h₂' ∈ Set.Ioo (dL2 p * Δh p .one + hstar p .two) (dU1 p * Δh p .one + hstar p .two))
    (S : ℝ) (hS : S ∈ Set.Icc 0 p.U) (hroot : f1 p S h₂' = 0) :
    ∀ x ∈ Set.Icc 0 S, 0 ≤ F2 p S x h₂' := by sorry

end DriftVarCtrl.FixedLB
