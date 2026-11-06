-- Prove2me | Theorems.Thm_BianchiIX_norm_le_exp_of_faster_forcing
-- name    : BianchiIX.norm_le_exp_of_faster_forcing
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T15:11:02.065573+00:00
-- url     : https://prove2.me/theorems/05e56fca-641c-4337-95d1-3c8521ac138c
-- title:
--   A contractive linear equation retains its decay under faster forcing
-- statement:
--   For a finite index type $\iota$, a real matrix $A=(A_{ij})$, and $i\in\iota$,
--   define its signed row sum by
--   $$\sigma_i(A)=A_{ii}+\sum_{j\ne i}|A_{ij}|.$$
--   Vectors in $\mathbb R^\iota$ carry the supremum norm.
--   Let $f,q:\mathbb R\to\mathbb R^\iota$,
--   $A:\mathbb R\to\mathbb R^{\iota\times\iota}$, $\rho>0$ and $Q\geq0$.
--   On $[0,T]$, assume $f'=Af+q$, every signed row sum of $A$ is at most
--   $-\rho$, and $\|q(t)\|_\infty\leq Qe^{-2\rho t}$.
--   Then for every $t\in[0,T]$,
--   $$\|f(t)\|_\infty\leq(\|f(0)\|_\infty+Q/\rho)e^{-\rho t}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ContractiveForcing.lean#L11-L63

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open BianchiIX
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem BianchiIX.norm_le_exp_of_faster_forcing {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {ρ Q T : ℝ} (hρ : 0 < ρ) (hQ : 0 ≤ Q)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Icc 0 T, ∀ i, signedRowSum (A t) i ≤ -ρ)
    (hq : ∀ t ∈ Icc 0 T, ‖q t‖ ≤ Q * Real.exp (-2 * ρ * t)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ (‖f 0‖ + Q / ρ) * Real.exp (-ρ * t) := by sorry
