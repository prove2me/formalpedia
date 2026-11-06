-- Prove2me | Theorems.Thm_BianchiIX_reciprocalProfile_derivative_bounds
-- name    : BianchiIX.reciprocalProfile_derivative_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T16:24:03.262774+00:00
-- url     : https://prove2.me/theorems/013cfdf9-656b-4f24-85f9-1e2429dc0dfd
-- title:
--   Derivative bounds after reciprocal compactification
-- statement:
--   For $y=(m,w)$ with $m\geq3/2$, set $a=(m+1)^{-1}$ and
--   $h(y)=(a,w)$. Let $B\geq0$ and let $g:\mathbb R^2\to\mathbb R$ be
--   $C^2$ at $h(y)$, with $|g|,\|dg\|,\|d^2g\|\leq B$ there.
--   For $f(y)=a\,g(h(y))$,
--   $$|f(y)|\leq Ba,\quad\|df_y\|\leq2Ba,\quad\|d^2f_y\|\leq7Ba.$$
--   All norms are induced by the sup norm.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ReciprocalProfileBounds.lean#L7-L80

import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Fin.VecNotation

noncomputable section
open BianchiIX

theorem BianchiIX.reciprocalProfile_derivative_bounds {g : (Fin 2 → ℝ) → ℝ} {y : Fin 2 → ℝ} {B : ℝ}
    (hy : 3 / 2 ≤ y 0) (hB : 0 ≤ B)
    (hg : ContDiffAt ℝ 2 g (reciprocalParameterMap y))
    (hg0 : |g (reciprocalParameterMap y)| ≤ B)
    (hg1 : ‖fderiv ℝ g (reciprocalParameterMap y)‖ ≤ B)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (reciprocalParameterMap y)‖ ≤ B) :
    |reciprocalParameter y * g (reciprocalParameterMap y)| ≤ B * reciprocalParameter y ∧
      ‖fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z)) y‖ ≤
        2 * B * reciprocalParameter y ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z))) y‖ ≤
        7 * B * reciprocalParameter y := by sorry
