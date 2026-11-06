-- Prove2me | Theorems.Thm_BianchiIX_norm_le_gronwall_uIcc
-- name    : BianchiIX.norm_le_gronwall_uIcc
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:17:29.682214+00:00
-- url     : https://prove2.me/theorems/0ff72da4-2dea-4c53-97fa-f9329a5af3bf
-- title:
--   A Gronwall norm bound in either time direction
-- statement:
--   For real $\delta,K,\varepsilon,\ell$, let
--   $$G(\delta,K,\varepsilon,\ell)=
--   \begin{cases}
--   \delta+\varepsilon\ell,&K=0,\\
--   \delta e^{K\ell}+\varepsilon(e^{K\ell}-1)/K,&K\ne0.
--   \end{cases}$$
--   Write $[s,t]_{\mathrm{u}}=[\min(s,t),\max(s,t)]$.
--   Let $f,df:\mathbb R\to\mathbb R^5$, with the
--   finite-product norm. Suppose $f'(u)=df(u)$ on $[t_0,t]_{\mathrm u}$,
--   $\|f(t_0)\|\leq\delta$, and
--   $$\|df(u)\|\leq K\|f(u)\|+\varepsilon\quad(u\in[t_0,t]_{\mathrm u}).$$
--   Then $\|f(t)\|\leq G(\delta,K,\varepsilon,|t-t_0|)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/VariationRemainder.lean#L10-L33

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

theorem BianchiIX.norm_le_gronwall_uIcc {f df : ℝ → NormalizedState} {t₀ t δ K ε : ℝ}
    (hf : ∀ u ∈ uIcc t₀ t, HasDerivAt f (df u) u)
    (hinit : ‖f t₀‖ ≤ δ)
    (hbound : ∀ u ∈ uIcc t₀ t, ‖df u‖ ≤ K * ‖f u‖ + ε) :
    ‖f t‖ ≤ gronwallBound δ K ε |t - t₀| := by sorry
