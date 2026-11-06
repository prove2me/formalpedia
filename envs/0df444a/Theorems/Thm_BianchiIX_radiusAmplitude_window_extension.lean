-- Prove2me | Theorems.Thm_BianchiIX_radiusAmplitude_window_extension
-- name    : BianchiIX.radiusAmplitude_window_extension
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:29:28.865198+00:00
-- url     : https://prove2.me/theorems/5e5e1726-dca7-41e0-9e45-24a099ae7448
-- title:
--   Positive amplitude extensions on a closed output-radius window
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--
--   For real functions $f,d_f$ and real endpoints $l,r$, define $F$ and $V$ by
--   $$F(x)=\begin{cases}
--   \mathcal R_{f(l),d_f(l),-1}(x-l),&x<l,\\
--   \mathcal R_{f(r),d_f(r),1}(x-r),&x\geq l,\ r<x,\\
--   f(x),&\text{otherwise},
--   \end{cases}$$
--   $$V(x)=\begin{cases}
--   d_f(l)\chi(-(x-l)/f(l)),&x<l,\\
--   d_f(r)\chi((x-r)/f(r)),&x\geq l,\ r<x,\\
--   d_f(x),&\text{otherwise}.
--   \end{cases}$$
--   Write $F_f,V_f$ when comparing several pairs of input functions.
--
--   For real functions $U,d_U$, set
--   $$r_U(x)=\sqrt{U(x)},\qquad b_U(x)=\frac{d_U(x)}{2\sqrt{U(x)}}.$$
--   Let $F_U,V_U$ be the root-curve construction applied to $(r_U,b_U)$, and set
--   $$\widetilde U(x)=F_U(x)^2.$$
--   For another pair $W,d_W$, use the analogous notation.
--
--   Let $g=\operatorname{invFunOn}k\,[a,b]$,
--   $A(t)=U(g(t))$, and $V(t)=U'(g(t))/k'(g(t))$.
--   Denote by $\mathfrak E_{k,U}^{a,b;l,r}$ the canonical amplitude extension
--   of $A,V$ from $[l,r]$, and by $\mathfrak E_{k,U}^{a,b}$ the extension
--   from $[k(b),k(a)]$.
--   Suppose $a<b$, $l<r$,
--   $[l,r]\subset[k(b),k(a)]$, and $\theta\leq1$.
--   On $[a,b]$, assume $k,U,W$ are $C^1$, $k'<0$, $U,W>0$,
--   $U+W\leq B$, and
--   $$|U'|\leq\theta\sqrt U\,|k'|,\qquad
--   |W'|\leq\theta\sqrt W\,|k'|.$$
--   Then $u=\mathfrak E_{k,U}^{a,b;l,r}$ and
--   $w=\mathfrak E_{k,W}^{a,b;l,r}$ are globally $C^1$ and, whenever
--   $x\in[a,b]$ and $k(x)\in[l,r]$,
--   $$u(k(x))=U(x),\quad w(k(x))=W(x),\quad
--   u'(k(x))=U'(x)/k'(x),\quad w'(k(x))=W'(x)/k'(x).$$
--   For every real $t$, $u(t),w(t)>0$, $u(t)+w(t)\leq25B/16$,
--   $|u'(t)|\leq\theta\sqrt{u(t)}$, $|w'(t)|\leq\theta\sqrt{w(t)}$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RadiusAmplitudeWindow.lean#L12-L71

import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.radiusAmplitude_window_extension {k U W : ℝ → ℝ} {a b l r θ B : ℝ}
    (hab : a < b) (hlr : l < r) (hwindow : Icc l r ⊆ Icc (k b) (k a)) (hθ : θ ≤ 1)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ θ * (Real.sqrt (U x) * |deriv k x|))
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ θ * (Real.sqrt (W x) * |deriv k x|))
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeWindowExtension k U a b l r
    let w := radiusAmplitudeWindowExtension k W a b l r
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, k x ∈ Icc l r →
        u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ θ * Real.sqrt (u x) ∧ |deriv w x| ≤ θ * Real.sqrt (w x) := by sorry
