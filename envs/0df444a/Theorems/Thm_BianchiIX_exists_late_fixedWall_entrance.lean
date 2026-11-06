-- Prove2me | Theorems.Thm_BianchiIX_exists_late_fixedWall_entrance
-- name    : BianchiIX.exists_late_fixedWall_entrance
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:08:37.900306+00:00
-- url     : https://prove2.me/theorems/b5fc11f3-1e1c-4cac-a83e-ee481c84681e
-- title:
--   A fixed-height entrance for Taub-avoiding orbits with small wall products
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--
--   For a fixed initial time $t_0$, put
--   $$\mathcal D_{t_0}=\{(x,t):t\in I_{\max}(x,t_0)\},\qquad
--   \Phi_{t_0}(x,t)=\alpha_{x,t_0}(t),\qquad
--   J_{x,t_0}(t)=d_x\Phi_{t_0}(x,t).$$
--
--   Write $\lambda_x=d\mathcal C_x:X\to\mathbb R$ for the constraint differential.
--
--   For $x=(p,s,a,b,c)$, define
--   $$H(x)=(abc)^{2/3},\quad w(x)=abc(1+4H(x)),\quad
--   \delta(x)=2K-3S,\quad \bar\delta(x)=\frac{2(K+4H(x))}{1+4H(x)},$$
--   $$V(x,t_0,t)=\frac{w(x)\det J_{x,t_0}(t)}{w(\alpha_{x,t_0}(t))}.$$
--   Write $[L]$ for the matrix of a continuous linear operator $L:X\to X$
--   in the standard basis. Set $\Omega(v_0,\ldots,v_4)=\det(v_0,\ldots,v_4)$,
--   $$\omega_x(v_0,\ldots,v_3)=\frac{\Omega(x/2,v_0,\ldots,v_3)}{w(x)},\qquad
--   \varphi_x(v_0,v_1,v_2)=\omega_x(F(x),v_0,v_1,v_2).$$
--
--   A normalized symmetry is a continuous linear equivalence $L:X\to X$ satisfying
--   $$\mathcal C(Lx)=\mathcal C(x),\quad Lx\in W\ \Longleftrightarrow\ x\in W,
--   \quad F(Lx)=LF(x),\quad w(Lx)=w(x),\quad\det L=1.$$
--   These symmetries include the identity, composition, inverse, and the two maps
--   $$R(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a),\qquad
--   S_0(p,s,a,b,c)=(p,-s,a,c,b).$$
--   Transforming a solution replaces its curve $\alpha$ by $L\alpha$ and
--   keeps its time domain.
--
--   Write $\Phi^s_t(x)=\alpha_{x,s}(t)$, with domain $I(x,s)$, and
--   $\mathcal X=\{x:\mathcal C(x)=1,\ N_i(x)>0\ (i=1,2,3)\}$.
--   For $y=(v,l,r)\in\mathbb R^3$ and a wall height $h$, put
--   $$b=e^{-l},\quad c=e^{-r},\quad d=1-v^2-K(h,b,c),\quad
--   U_h=\{y:d>0\},\quad c_h(y)=(-\sqrt d,v,h,b,c).$$
--   For a normalized axis symmetry $A$, the chart is $c_{A,h}=A^{-1}c_h$,
--   with coordinates $\pi_A(x)=((Ax)_1,-\log (Ax)_3,-\log (Ax)_4)$.
--   At $p=-\sqrt d$ its flux density and measure are
--   $$\rho_h(y)=\frac{p^2+v^2-2p}{2|p|(1+4(hbc)^{2/3})},
--   \qquad d\mu_h={\bf1}_{U_h}\rho_h^+\,dy.$$
--   Write $\varphi$ for the signed section flux and $\bar\delta$ for the
--   corrected divergence. The three primary frames interchange axis zero
--   with the chosen dominant axis.
--
--   Write $x_t=\Phi^0_t(x)$, $d_T(x)=\min_i|x-T_i|_2$ for the distance to
--   the three Taub points, and $V_\epsilon(x)$ for $d_T(x_t)\ge\epsilon$
--   at every existing $t\ge0$. Write $D_\Delta(x)$ if $4N_iN_j\le\Delta^2$
--   for all distinct walls, and $u_i$ for their logarithmic rates:
--   $\dot N_i=u_iN_i$. In the primary frame put $r_T^2=s^2+(b-c)^2$.
--
--   For every $\epsilon>0$ there are $0<\nu_0\le1/4$, $0<c\le1$.
--   For $0<\nu\le\nu_0$, $0\le\Delta\le\nu/8$, take $x\in\mathcal X$
--   with $V_\epsilon(x)$ and $D_\Delta(x_u)$ for all $u\ge0$. At some
--   $s\in[0,5/\nu^2]$ all walls are below $\nu$. They stay below on
--   $[s,T)$ until the first existing wall hit $T>s$. Precisely one wall
--   $N_i$ then equals $\nu$, $u_i(x_T)\ge c$, and
--   $N_i'(T)=u_i(x_T)\nu\ge c\nu>0$ along the orbit.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/LateWallEntrance.lean#L10-L76

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_late_fixedWall_entrance {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ > (0 : ℝ), ν₀ ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ν / 8 →
        ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
          normalizedTaubAvoidance ε x →
          (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
          ∃ s ∈ Icc 0 (5 / ν ^ 2), ∃ T > s, ∃ i : Fin 3,
            (∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 s) < ν) ∧
            IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
              ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} T ∧
            (∀ u ∈ Ico s T, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 u) < ν) ∧
            wallValue i (normalizedMaxCurve x 0 T) = ν ∧
            (∀ j : Fin 3, j ≠ i → wallValue j (normalizedMaxCurve x 0 T) < ν) ∧
            c ≤ wallRate i (normalizedMaxCurve x 0 T) ∧
            HasDerivAt (fun u => wallValue i (normalizedMaxCurve x 0 u))
              (wallRate i (normalizedMaxCurve x 0 T) * ν) T ∧
            0 < c * ν ∧ c * ν ≤ wallRate i (normalizedMaxCurve x 0 T) * ν := by sorry
