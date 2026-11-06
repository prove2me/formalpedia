-- Prove2me | Theorems.Thm_BianchiIX_exitSinglePhase_differential
-- name    : BianchiIX.exitSinglePhase_differential
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T18:59:46.044767+00:00
-- url     : https://prove2.me/theorems/50337416-c0d1-43c5-9605-35797b6e6544
-- title:
--   Exact differential of the exit single-wall radical phase
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
--
--   Define
--   $$H_0=(2-g(R,v))^2+v^2,\quad d_0=(u-w)^2-2v(u+w),$$
--   $$e=d_0[1+(R^2-4+d_0)/H_0],\qquad
--   \sigma_v(R,u,w)=(\sqrt{R^2+e}-2)/2.$$
--   Put
--   $$H_{0,R}=2(g-2)R/g,\quad
--   e_R=d_0[2R/H_0-(R^2-4+d_0)H_{0,R}/H_0^2],$$
--   $$e_{\rm wall}=1+(R^2-4+2d_0)/H_0.$$
--   Assume $v^2<R^2$, $H_0\ne0$,
--   $R^2+e>0$. Then $\sigma_v$ is $C^2$ at $(R,u,w)$ and
--   $$d\sigma_v(d)=\frac{(2R+e_R)d_R+
--   e_{\rm wall}[(2(u-w)-2v)d_u+(-2(u-w)-2v)d_w]}
--   {4\sqrt{R^2+e}}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitSinglePhaseDifferential.lean#L17-L56

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX

theorem BianchiIX.exitSinglePhase_differential {v : ℝ} {Y : ExitTailState}
    (hg : v ^ 2 < (Y 0) ^ 2) (hH : exitSingleBase (Y 0) v ≠ 0)
    (hS : 0 < (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2)) :
    ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) Y ∧
      ∀ d : ExitTailState,
      fderiv ℝ (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) Y d =
        ((2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) * d 0 +
          exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2) *
            ((2 * (Y 1 - Y 2) - 2 * v) * d 1 + (-2 * (Y 1 - Y 2) - 2 * v) * d 2)) /
          (4 * Real.sqrt ((Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2))) := by sorry
