-- Prove2me | Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock_forcing
-- name    : BianchiIX.norm_le_exp_of_norm_deriv_clock_forcing
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:54:57.184903+00:00
-- url     : https://prove2.me/theorems/421a773a-4e32-4a55-905a-da0ab6918afd
-- title:
--   Constant forcing contributes only its elapsed-time budget
-- statement:
--   Let $E$ be a real normed space, let $f:\mathbb R\to E$
--   and $z:\mathbb R\to\mathbb R$ have derivatives at every point of
--   $[a,b]$, and let $\varepsilon\geq0$. Suppose $z(t)\geq z(a)$ and
--   $$\|f'(t)\|\leq z'(t)\|f(t)\|+\varepsilon\quad(t\in[a,b]).$$
--   Then throughout $[a,b]$,
--   $$\|f(t)\|\leq(\|f(a)\|+\varepsilon(t-a))\exp(z(t)-z(a)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/NormClockForcing.lean#L11-L49

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

theorem BianchiIX.norm_le_exp_of_norm_deriv_clock_forcing {f f' : ℝ → E} {z z' : ℝ → ℝ} {a b ε : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hε : 0 ≤ ε) (hclock : ∀ t ∈ Icc a b, z a ≤ z t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖ + ε) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ (‖f a‖ + ε * (t - a)) * Real.exp (z t - z a) := by sorry
