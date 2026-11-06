-- Prove2me | Theorems.Thm_BianchiIX_exists_axisFamily_firstReturn
-- name    : BianchiIX.exists_axisFamily_firstReturn
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T03:36:55.438194+00:00
-- url     : https://prove2.me/theorems/c14c05b0-ce0c-410e-b34b-e1c89baca21c
-- title:
--   Exact flux transport by the first return to a finite wall family
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
--   For target frames $B_i$, heights $k_i$, and coordinate sets $E_i$ put
--   $c(i,y)=c_{B_i,k_i}(y)$, $E^\sqcup=\{(i,y):y\in E_i\}$ and
--   $\nu_k=\sum_i(y\mapsto(i,y))_*\mu_{k_i}$.
--   A hit from $z=(i,y)$ at time $t$ starts with $y\in U_{k_i}$ at $t_0$,
--   exists in the maximal domain, and reaches a target frame with its first
--   wall at the prescribed height, negative first shear, and coordinates in
--   the corresponding target set. Write $H(z)$ for these times $t>t_0$,
--   and $D_E=\{z\in E^\sqcup:H(z)\ne\varnothing\}$.
--   A wall arrival atlas from $(A,h)$ gives countably many injective $C^1$
--   branches covering each crossing time in each target chart.
--   For a branch $q=(i,n)$ with map $R_q$ and time $\tau_q$, put
--   $$j_q(y)=\rho_{k_i}(R_qy)|\det DR_q(y)|/\rho_h(y).$$
--   Given a time set $I$, an eligible point lies on the branch, has time in
--   $I$ and target in $E_i$. Its delay is $(\tau_q-t_0)^+$ there and
--   $+\infty$ otherwise. The first piece $L_q$ consists of eligible points
--   attaining the infimum of all delays with the least branch encoding.
--
--   Let the nonempty label type be finite and encodable with measurable
--   singletons. Suppose $k_i,\varepsilon_i>0$ and $E_i$ are measurable
--   with $(c_{k_i}(z))_0\le-\varepsilon_i$ on $E_i$, and $c$ is injective
--   on $E^\sqcup$. There exist measurable total maps $R$ on labelled
--   coordinates and $j$ into $[0,\infty]$ such that $R$ is injective on
--   $D_E$. For each $z\in D_E$, $H(z)$ has a least element $t$,
--   $R(z)\in E^\sqcup$, $c(R(z))=\Phi^{t_0}_t(c(z))$, and $1<j(z)<\infty$.
--   For measurable $S\subset D_E$, $R(S)$ is measurable and
--   $$\nu_k(R(S))=\int_S j\,d\nu_k.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/AxisReturnMeasure.lean#L92-L132

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.exists_axisFamily_firstReturn {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (R : ι × SectionCoordinates → ι × SectionCoordinates) (j : ι × SectionCoordinates → ℝ≥0∞),
      Measurable R ∧ Measurable j ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, 1 < j z ∧ j z < ∞) ∧
      ∀ S, MeasurableSet S → S ⊆ axisFamilyReturnDomain B k t₀ E →
        MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ z in S, j z ∂axisFamilyMeasure k := by sorry
