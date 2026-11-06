-- Prove2me | Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
-- name    : BianchiIX.norm_le_exp_of_norm_deriv_clock
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:02:39.953551+00:00
-- url     : https://prove2.me/theorems/e97298f5-35ef-4a05-b471-0a188c69aa74
-- title:
--   A primitive of the growth rate controls a normed-space curve
-- statement:
--   Let $E$ be a real normed space and $f:\mathbb R\to E$,
--   $z:\mathbb R\to\mathbb R$. Suppose they have derivatives $f'(t),z'(t)$
--   at every $t\in[a,b]$, and $\|f'(t)\|\leq z'(t)\|f(t)\|$ there.
--   Then, for every $t\in[a,b]$,
--   $$\|f(t)\|\leq\|f(a)\|\exp(z(t)-z(a)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/NormClockGrowth.lean#L14-L45

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.norm_le_exp_of_norm_deriv_clock {f f' : ℝ → E} {z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (z t - z a) := by sorry
