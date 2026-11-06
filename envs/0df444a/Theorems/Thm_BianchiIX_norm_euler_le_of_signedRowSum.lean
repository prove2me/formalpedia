-- Prove2me | Theorems.Thm_BianchiIX_norm_euler_le_of_signedRowSum
-- name    : BianchiIX.norm_euler_le_of_signedRowSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:34:14.898233+00:00
-- url     : https://prove2.me/theorems/effab83f-cd97-4abb-b582-4027b34d4b99
-- title:
--   An Euler-step supremum-norm estimate from signed row sums
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
--   Assume $\iota$ is nonempty. Let $h\geq0$,
--   $\sigma_i(A)\leq\rho$, and $1+hA_{ii}\geq0$ for every $i$.
--   Then for every $x\in\mathbb R^\iota$,
--   $$\|x+hAx\|_\infty\leq(1+h\rho)\|x\|_\infty.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SignedRowGrowth.lean#L19-L50

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

theorem BianchiIX.norm_euler_le_of_signedRowSum {A : Matrix ι ι ℝ} {ρ h : ℝ}
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hh : 0 ≤ h)
    (hdiag : ∀ i, 0 ≤ 1 + h * A i i) (x : ι → ℝ) :
    ‖x + h • A.mulVec x‖ ≤ (1 + h * ρ) * ‖x‖ := by sorry
