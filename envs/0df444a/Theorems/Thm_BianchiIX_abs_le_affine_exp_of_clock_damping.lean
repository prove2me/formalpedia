-- Prove2me | Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
-- name    : BianchiIX.abs_le_affine_exp_of_clock_damping
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:57:48.9755+00:00
-- url     : https://prove2.me/theorems/b9b7f225-af80-4fdb-ac54-fa0873cfc1f8
-- title:
--   A damped scalar equation with a decaying forcing envelope in a monotone clock
-- statement:
--   Let $a,b,c,B\in\mathbb R$. Suppose on $[a,b]$
--   $$f'(t)=z'(t)\bigl(d(t)f(t)+g(t)\bigr),\qquad z'(t)\geq0,
--   \qquad d(t)\leq-c,$$
--   $$|g(t)|\leq B e^{-c(z(t)-z(a))}.$$
--   Here both displayed derivatives exist at every point of the closed
--   interval. Then, for every $t\in[a,b]$,
--   $$|f(t)|\leq e^{-c(z(t)-z(a))}
--   \bigl(|f(a)|+B(z(t)-z(a))\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/DampedForcing.lean#L59-L118

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.abs_le_affine_exp_of_clock_damping {f d g z z' : ℝ → ℝ} {a b c B : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t + g t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ B * Real.exp (-c * (z t - z a))) :
    ∀ t ∈ Icc a b, |f t| ≤ Real.exp (-c * (z t - z a)) * (|f a| + B * (z t - z a)) := by sorry
