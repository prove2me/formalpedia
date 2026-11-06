-- Prove2me | Theorems.Thm_BianchiIX_mainWallOriginalMeasure_radialFailure_le_regions
-- name    : BianchiIX.mainWallOriginalMeasure_radialFailure_le_regions
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:07:39.4262+00:00
-- url     : https://prove2.me/theorems/478f8dff-3bdc-420f-b1ad-48abaed4916b
-- title:
--   Original flux of the radial failure bounded by two corrected fluxes
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
--   In wall coordinates $y=(v,l,r)$ put $u=e^{-l}$, $w=e^{-r}$,
--   $M=\max(u,w)$, $S_d^\circ=\{|v|,M<d\}$, and let $S_d$ use weak
--   inequalities. Put $R=|v|$ when $M\le\epsilon|v|$ and $R=M$ otherwise.
--   For $a=a_j=d2^{-j-1}$ and $a<\rho<2a$, $\rho<d$, there are four
--   charts $L_k$ with domains $D_{kj}$. The two shear charts send
--   $(\rho,u,w)$ to $(\pm\rho,-\log u,-\log w)$ for $u,w>0$,
--   $M\le\epsilon\rho$. The angular chart sends $(\rho,\theta,\zeta)$
--   to $(\theta\rho,-\log\rho,-\log\zeta)$, with $|\theta|<L=1/\epsilon$,
--   $|\theta|\rho<d$ and $0<\zeta\le\rho$. Its reflected chart composes
--   with $(v,l,r)\mapsto(-v,r,l)$ and has $\zeta<\rho$.
--
--   The selected angular labels satisfy $|\theta|\le L$, $0<\zeta\le a^P$;
--   their budget is $51200(L+1)\zeta/a^3$. The shear labels have
--   $0<u,w\le2\epsilon a$, $\min(u,w)\le a^P$, with budget $800uw/a^4$.
--   Order the shear label as $(w,u)$ on the negative branch and $(u,w)$
--   on the positive one. Write $s_j=(q/2)\log(1/a_j)$. Let $F_{kj}$
--   contain points with $\rho\in[a,2a]$ whose label is unselected or whose
--   budget and actual restart core at $(h,s_j)$ lie outside the typical
--   survivor domain for $(\eta,J,\sigma,B_{\rm cap})$. The section failure
--   is $F=H\cup\bigcup_{kj}L_k(D_{kj}\cap F_{kj})$, where
--   $H=S_d^\circ\cap\bigcup_j\{R=2a_j\}$. The comparison regions
--   $A(B_A),S(B_S)$ consist of the corresponding dyadic unions of the
--   symmetrized selected failure layers at those caps and the unselected layers.
--
--   Suppose $0<d\le1$, $0\le\epsilon\le1/128$, $0\le L=1/\epsilon$
--   (with totalized inverse), $P\ge4$, $B_{\rm cap}\le1$,
--   $800d\le B_{\rm cap}$ and $51200(L+1)d\le B_{\rm cap}$.
--
--   Suppose also $0<h$, $d\le h$ and $F$ is measurable. Write $\mu_h^o$
--   for the original flux on $U_h$, of density $[(p^2+v^2-2p)/(2|p|)]^+$.
--   For any $B_A,B_S$,
--   $$\mu_h^o(F)\le(1+4h^2)\bigl(\mu_h(A(B_A))+\mu_h(S(B_S))\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/RadialFailureComparison.lean#L160-L185

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.mainWallOriginalMeasure_radialFailure_le_regions {h q d ε P η σ Bcap BA BS : ℝ} {J : ℕ}
    (hh : 0 < h) (hd : 0 < d) (hd1 : d ≤ 1) (hdh : d ≤ h)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hL : 0 ≤ 1 / ε) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hS : 800 * d ≤ Bcap) (hA : 51200 * (1 / ε + 1) * d ≤ Bcap)
    (hE : MeasurableSet (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap))) :
    mainWallOriginalMeasure h (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) ≤
      ENNReal.ofReal (1 + 4 * h ^ 2) *
        (mainWallMeasure h (angularFailureRegion h q d (1 / ε) P η J σ BA) +
          mainWallMeasure h (shearFailureRegion h q d ε P η J σ BS)) := by sorry
