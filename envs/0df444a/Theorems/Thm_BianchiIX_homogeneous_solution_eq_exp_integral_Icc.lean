-- Prove2me | Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
-- name    : BianchiIX.homogeneous_solution_eq_exp_integral_Icc
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:55:21.014039+00:00
-- url     : https://prove2.me/theorems/8d2c4070-8b73-4419-bcc9-96e5bc35b9b5
-- title:
--   The scalar integrating-factor formula on a closed segment
-- statement:
--   Let $a\leq b$, and let $f,r:\mathbb R\to\mathbb R$
--   be continuous on $[a,b]$. If $f'(t)=r(t)f(t)$ for $a<t<b$, then
--   $$f(b)=f(a)\exp\left(\int_a^b r(t)\,dt\right).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ScalarMultiplier.lean#L9-L37

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.homogeneous_solution_eq_exp_integral_Icc {f r : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : ContinuousOn r (Icc a b)) (hc : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (r t * f t) t) :
    f b = f a * Real.exp (∫ t in a..b, r t) := by sorry
