-- Prove2me | Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
-- name    : BianchiIX.norm_slope_right_le_of_signedRowSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:37:11.27483+00:00
-- url     : https://prove2.me/theorems/35be6207-b107-4e54-8c53-ddfaa1e71091
-- title:
--   The forward norm slope is controlled by signed row sums
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
--   Assume $\iota$ is nonempty and
--   $f:\mathbb R\to\mathbb R^\iota$ has derivative $Af(t)$ at $t$.
--   If $\sigma_i(A)\leq\rho$ for every $i$ and
--   $R>\rho\|f(t)\|_\infty$, then for all $s>t$ sufficiently near $t$,
--   $$\frac{\|f(s)\|_\infty-\|f(t)\|_\infty}{s-t}<R.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SignedRowGrowth.lean#L52-L82

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

theorem BianchiIX.norm_slope_right_le_of_signedRowSum {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} (hf : HasDerivAt f (A.mulVec (f t)) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by sorry
