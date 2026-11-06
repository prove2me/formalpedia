-- Prove2me | Theorems.Thm_BianchiIX_norm_le_initial_of_signedRowSum_nonpos
-- name    : BianchiIX.norm_le_initial_of_signedRowSum_nonpos
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:38:41.125383+00:00
-- url     : https://prove2.me/theorems/4f86e9b1-28c7-4ba6-bcb4-fb54fa1127f1
-- title:
--   Nonpositive signed row sums bound the solution by its initial norm
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
--   Assume $\iota$ is nonempty. Let $f$ be
--   continuous on $[a,b]$ and satisfy $f'(t)=A(t)f(t)$ at every
--   $t\in[a,b)$. If $\sigma_i(A(t))\leq0$ for every such $t$ and every $i$,
--   then
--   $$\|f(t)\|_\infty\leq\|f(a)\|_\infty\quad(t\in[a,b]).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SignedRowGrowth.lean#L84-L96

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

theorem BianchiIX.norm_le_initial_of_signedRowSum_nonpos {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ := by sorry
