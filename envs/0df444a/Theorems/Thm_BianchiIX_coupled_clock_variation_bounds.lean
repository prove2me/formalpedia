-- Prove2me | Theorems.Thm_BianchiIX_coupled_clock_variation_bounds
-- name    : BianchiIX.coupled_clock_variation_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T16:25:33.905012+00:00
-- url     : https://prove2.me/theorems/834dc10c-2bc2-469a-9a61-64eb4e02ed9b
-- title:
--   Closing a scalar phase coupled to two transverse variations
-- statement:
--   For $C,A\geq0$ define
--   $$S_{C,A,x,y}(c)=|c_1||x|+|c_2||y|+CA(|c_1|+|c_2|),$$
--   $$K_{C,l}(c)=(C+1)(|c_0|+l(|c_1|+|c_2|)).$$
--   Let $s\leq t$, $C,A\geq0$, and let $q\geq0$
--   and $c:[s,t]\to\mathbb R^3$ be continuous. Suppose $l'=q$, $l(s)=0$,
--   $Z$ is differentiable and $Z'=q(c_0Z+c_1f_0+c_2f_1)$. Assume
--   $$|f_0(r)-f_0(s)|+|f_1(r)-f_1(s)|
--   \leq C\left(A+\int_s^r|Z|q\right).$$
--   If $\int_s^t S_{C,A,f_0(s),f_1(s)}(c)q\leq B$ and
--   $\int_s^t K_{C,l}(c)q\leq\Lambda<1$, set $M=(|Z(s)|+B)/(1-\Lambda)$.
--   For every $r\in[s,t]$,
--   $$|Z(r)|\leq M,\quad |Z(r)-Z(s)|\leq B+\Lambda M,$$
--   $$|f_0(r)-f_0(s)|+|f_1(r)-f_1(s)|\leq C(A+l(r)M).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoupledClockVariation.lean#L15-L103

import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.coupled_clock_variation_bounds
    {Z Z' q l : ℝ → ℝ} {f : ℝ → Fin 2 → ℝ} {c : ℝ → Fin 3 → ℝ} {s t C A B Λ : ℝ}
    (hst : s ≤ t) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hZ : ∀ r ∈ Icc s t, HasDerivAt Z (Z' r) r)
    (hl : ∀ r ∈ Icc s t, HasDerivAt l (q r) r) (hls : l s = 0)
    (hqc : ContinuousOn q (Icc s t)) (hq : ∀ r ∈ Icc s t, 0 ≤ q r)
    (hcc : ContinuousOn c (Icc s t))
    (heq : ∀ r ∈ Icc s t, Z' r = q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1))
    (htrans : ∀ r ∈ Icc s t, |f r 0 - f s 0| + |f r 1 - f s 1| ≤
      C * (A + ∫ z in s..r, |Z z| * q z))
    (hsource : (∫ r in s..t, coupledVariationSource C A (f s 0) (f s 1) (c r) * q r) ≤ B)
    (hbudget : (∫ r in s..t, coupledVariationFeedback C (l r) (c r) * q r) ≤ Λ)
    (hΛ : Λ < 1) :
    ∀ r ∈ Icc s t,
      |Z r| ≤ (|Z s| + B) / (1 - Λ) ∧
      |Z r - Z s| ≤ B + Λ * ((|Z s| + B) / (1 - Λ)) ∧
      |f r 0 - f s 0| + |f r 1 - f s 1| ≤ C * (A + l r * ((|Z s| + B) / (1 - Λ))) := by sorry
