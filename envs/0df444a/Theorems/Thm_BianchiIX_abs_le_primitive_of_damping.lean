-- Prove2me | Theorems.Thm_BianchiIX_abs_le_primitive_of_damping
-- name    : BianchiIX.abs_le_primitive_of_damping
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:55:56.784945+00:00
-- url     : https://prove2.me/theorems/93c1dfc0-a41f-43a6-a629-223d63017a00
-- title:
--   A forcing primitive bounds a scalar solution with nonpositive damping
-- statement:
--   Let $f,p$ be continuous on $[a,b]$. Suppose for
--   every $t\in[a,b)$,
--   $$f'(t)=d(t)f(t)+g(t),\qquad p'(t)=q(t),\qquad
--   d(t)\leq0,\quad |g(t)|\leq q(t).$$
--   Then
--   $$|f(t)|\leq |f(a)|+p(t)-p(a)\qquad(t\in[a,b]).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/DampedForcing.lean#L45-L57

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

theorem BianchiIX.abs_le_primitive_of_damping {f d g p p' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ t ∈ Ico a b, HasDerivAt f (d t * f t + g t) t)
    (hp : ContinuousOn p (Icc a b)) (hdp : ∀ t ∈ Ico a b, HasDerivAt p (p' t) t)
    (hd : ∀ t ∈ Ico a b, d t ≤ 0) (hg : ∀ t ∈ Ico a b, |g t| ≤ p' t) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| + (p t - p a) := by sorry
