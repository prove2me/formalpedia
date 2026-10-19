-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_4
-- name    : DriftVarCtrl.FixedLB.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:28.615979+00:00
-- url     : https://prove2.me/theorems/4ce09451-1995-4beb-b458-d5c39336878b
-- title:
--   Lemma 4, p. EC-7 — f₁(S, h₂) = −(σ₁²/σ₂²) f₂(S, h₂)
-- statement:
--   Assume $v_1 < v_2$. For every $S \in [0,U]$ and every cost $h_2 > 0$,
--   $$f_1(S,h_2) = -\frac{\sigma_1^2}{\sigma_2^2}\,f_2(S,h_2),$$
--   where $f_1, f_2$ are the test functions (71) of the two-interval value.
--
--   This is equation (72): the two inequalities (68)–(69) become equalities at the same switching point, so a single root $S^*$ of $f_1$ handles both.
--
--   **Formalization Note.** $f_1, f_2$ are defined by derivatives of the explicit branches (70)–(71), so the identity is a genuine statement. The page says "Fix $h_1 > 0$"; $h_1 > 0$ is part of the model. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-7, Lemma 4 (proof of equation (72))

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Lemma 4, equation (72) (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-7). Fix `h₁ > 0`; then `f₁(S, h₂) = −(σ₁²/σ₂²) f₂(S, h₂)`.

Formalization Note: stated for `S ∈ [0, U]` (where the denominator of (87) is positive) and every cost
`h₂ > 0`; `f₁, f₂` are defined by (70)–(71) through `deriv`, so this is not definitional. The standing
`v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_4 (p : Params) (hv : v p .one < v p .two) (S : ℝ) (hS : S ∈ Set.Icc 0 p.U)
    (h₂' : ℝ) (hh₂ : 0 < h₂') :
    f1 p S h₂' = -(p.σ₁ ^ 2 / p.σ₂ ^ 2) * f2 p S h₂' := by sorry

end DriftVarCtrl.FixedLB
