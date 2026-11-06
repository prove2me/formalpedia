-- Prove2me | Theorems.Thm_BianchiIX_exists_exitTail_strict_prefix_bounds
-- name    : BianchiIX.exists_exitTail_strict_prefix_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T17:56:31.227738+00:00
-- url     : https://prove2.me/theorems/24f819fe-bee0-4849-9905-49b8937fb22d
-- title:
--   Improvement of the terminal-tail wall and radius bounds
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
--   For every $K\geq0$ there exist $A\geq2$ and
--   $0<\varepsilon\leq1$ such that the following holds. Let $T,\alpha,b\geq0$,
--   $b(1+T)\leq\varepsilon$, $\alpha T\leq K$, and
--   $Y'(s)=E_{e^{-s}}(Y(s))$ on $[0,T]$. Suppose $Y$ stays in
--   $\mathcal R_{\alpha,b,A,80A}$ and $|Y_1(0)|+|Y_2(0)|\leq b$.
--   Then, for both walls,
--   $$Y_{i+1}(T)=Y_{i+1}(0)M_i(Y,T),\qquad 2/A\leq M_i(Y,T)\leq A/2,$$
--   $$|Y_1(T)|+|Y_2(T)|\leq Ab/2,\qquad |Y_0(T)-Y_0(0)|\leq40Ab,$$
--   where $i=0,1$ corresponds to $s,w$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitTailBootstrap.lean#L48-L96

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_exitTail_strict_prefix_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ T α b : ℝ, ∀ Y : ℝ → ExitTailState,
      0 ≤ T → 0 ≤ α → 0 ≤ b → b * (1 + T) ≤ ε → α * T ≤ K →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y s)) →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ i : Fin 2,
        Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
        2 / A ≤ exitTailMultiplier Y i T ∧ exitTailMultiplier Y i T ≤ A / 2) ∧
      |Y T 1| + |Y T 2| ≤ A * b / 2 ∧ |Y T 0 - Y 0 0| ≤ 40 * A * b := by sorry
