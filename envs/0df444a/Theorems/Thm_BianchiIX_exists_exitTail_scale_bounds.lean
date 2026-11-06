-- Prove2me | Theorems.Thm_BianchiIX_exists_exitTail_scale_bounds
-- name    : BianchiIX.exists_exitTail_scale_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T18:00:37.329763+00:00
-- url     : https://prove2.me/theorems/0d2a4ecb-6c8b-44d0-8669-b338dd671ae6
-- title:
--   Uniform terminal-tail bounds at a power-dependent exit height
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
--   Fix $0<\eta\leq1$ and $J\geq1$. There exist
--   $A\geq2$ and $\varepsilon>0$ such that, if $0<\alpha\leq1$,
--   $0<b\leq\varepsilon\alpha^J$, $0\leq T\leq L(\eta,\alpha,J)$,
--   $Y'=E_{e^{-s}}(Y)$ on $[0,T]$, $Y_0(0)=2+2\alpha$ and
--   $|Y_1(0)|+|Y_2(0)|\leq b$, then every $r\in[0,T]$ satisfies
--   $$Y(r)\in\mathcal R_{\alpha,b,A,80A},\quad
--   Y_{i+1}(r)=Y_{i+1}(0)M_i(Y,r),\quad2/A\leq M_i(Y,r)\leq A/2,$$
--   $$|Y_1(r)|+|Y_2(r)|\leq Ab/2,\quad |Y_0(r)-Y_0(0)|\leq40Ab,$$
--   $$Y_0(r)>2+\alpha,\qquad |Y_1(r)|\leq e^{-r}/2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitTailScale.lean#L11-L68

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_exitTail_scale_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ α b T : ℝ, ∀ Y : ℝ → ExitTailState,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → (0 ≤ T ∧ T ≤ exitTailLength η α J) →
      Y 0 0 = 2 + 2 * α → |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ r ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y r) ∧
        (∀ i : Fin 2, Y r i.succ = Y 0 i.succ * exitTailMultiplier Y i r ∧
          2 / A ≤ exitTailMultiplier Y i r ∧ exitTailMultiplier Y i r ≤ A / 2) ∧
        |Y r 1| + |Y r 2| ≤ A * b / 2 ∧ |Y r 0 - Y 0 0| ≤ 40 * A * b ∧
        2 + α < Y r 0 ∧ |Y r 1| ≤ Real.exp (-r) / 2 := by sorry
