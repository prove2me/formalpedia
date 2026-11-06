-- Prove2me | Theorems.Thm_BianchiIX_exists_fixedWall_physical_core
-- name    : BianchiIX.exists_fixedWall_physical_core
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:09:44.343676+00:00
-- url     : https://prove2.me/theorems/7065dfff-91d8-461f-8edf-1ab2c4ab3ed8
-- title:
--   A growing fixed-height wall reaches a genuine core with quadratic error
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
--   For a projective state put $r(y)=\sqrt{(y_0-1)^2+y_2^2}$.
--   The reference entrance is $e(k,v)=(1+\sqrt{k^2-v^2},0,v,0)$;
--   $f(K)=\sqrt3/(4+(1+K)^2)$. Write $g(x)=(\Pi x)_2$ for the active
--   wall, $\Xi$ for the inverse projective chart, and $E(x)$ for the first
--   entrance data (return time, projective endpoint, normalized endpoint,
--   radius). For core coordinates $Y$ write $x(Y)=\Xi(e_+(Y))$,
--   $b(Y)=Y_1+Y_2$, and let $K_{N,\gamma}$ be the range
--   $2+2\gamma\le Y_0\le2N$, $\gamma\le Y_0/2-\lfloor Y_0/2\rfloor\le1-\gamma$.
--
--   At a framed endpoint $X$, put $Y=\Pi X$. The core bounds with
--   parameters $k,\epsilon,C,\Delta$ are $Y_2=1$, $Y_0>1$, $1+X_0>0$,
--   $|r(Y)-k|\le C\Delta^2$, $X_3\ge f(8/\epsilon)$, $Y_1,Y_3>0$,
--   and $Y_1+Y_3\le\Delta^2/(2f(8/\epsilon)^2)$.
--
--   Let $c,\epsilon,\nu>0$, $\nu\le1/4$, $\nu^2\le c/4$,
--   $\nu\le\epsilon^2/32$. There exist $\Delta_0>0$, $C\ge1$. If
--   $0\le\Delta\le\Delta_0$, $x\in\mathcal X$ has primary wall $\nu$,
--   primary rate at least $c$, $d_T(x)\ge\epsilon$, and $D_\Delta(x_u)$
--   for all $u\ge0$, some frame $Q$ and $2\le k<8/\epsilon$ have the
--   following property. From $z=Qx$ the least positive existing hit $T$ of
--   $g=1$ satisfies $T\le C$, $T\in I(x,0)$,
--   $X=\Phi^0_T(z)=Qx_T$ and the core bounds above. The time derivative of
--   the active wall at $T$ is the positive event rate, and $E$ is $C^2$ at $z$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/FixedWallPhysicalCore.lean#L10-L91

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_fixedWall_physical_core {c ε ν : ℝ}
    (hcpos : 0 < c) (hε : 0 < ε) (hν : 0 < ν) (hνmax : ν ≤ 1 / 4)
    (hνc : ν ^ 2 ≤ c / 4) (hνε : ν ≤ ε ^ 2 / 32) :
    ∃ Δ₀ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x → x 2 = ν →
        c ≤ rateOne (x 0) (x 1) →
        (∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) →
        (∀ u, 0 ≤ u → normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
        ∃ a : Fin 6, ∃ k T : ℝ, 2 ≤ k ∧ k < 8 / ε ∧ T ∈ normalizedMaxDomain x 0 ∧
          let z := (axisFrame a).map x
          let X := normalizedMaxCurve z 0 T
          let Y := toProjectiveState X
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain z 0 ∧ projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} T ∧
            T ≤ C ∧ X = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
            Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
            |coreRadius (Y 0) (Y 2) - k| ≤ C * Δ ^ 2 ∧
            referenceCoreWallFloor (8 / ε) ≤ X 3 ∧
            0 < Y 1 ∧ 0 < Y 3 ∧
            Y 1 + Y 3 ≤ Δ ^ 2 / (2 * referenceCoreWallFloor (8 / ε) ^ 2) ∧
            HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve z 0 t))
              (normalizedEventRate projectiveActiveWall z 0 T) T ∧
            0 < normalizedEventRate projectiveActiveWall z 0 T ∧
            ContDiffAt ℝ 2 physicalEntranceData z := by sorry
