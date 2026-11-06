-- Prove2me | Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
-- name    : BianchiIX.norm_le_exp_of_signedRowSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:40:41.394202+00:00
-- url     : https://prove2.me/theorems/00252ebb-f16b-4a1b-af0b-cb6aaf4c87ce
-- title:
--   Exponential comparison with a primitive of the signed row bound
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
--   Assume $\iota$ is nonempty. Let $f$ and
--   $z$ be continuous on $[a,b]$. For every $t\in[a,b)$ suppose
--   $$f'(t)=A(t)f(t),\qquad z'(t)=q(t),\qquad
--   \sigma_i(A(t))\leq q(t)\quad(i\in\iota).$$
--   Then
--   $$\|f(t)\|_\infty\leq\|f(a)\|_\infty e^{z(t)-z(a)}
--   \quad(t\in[a,b]).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SignedRowGrowth.lean#L112-L149

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem BianchiIX.norm_le_exp_of_signedRowSum {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hz : ContinuousOn z (Icc a b))
    (hzderiv : ∀ t ∈ Ico a b, HasDerivAt z (z' t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ z' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (z t - z a) := by sorry
