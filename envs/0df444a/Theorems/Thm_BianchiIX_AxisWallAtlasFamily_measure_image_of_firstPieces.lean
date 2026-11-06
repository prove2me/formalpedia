-- Prove2me | Theorems.Thm_BianchiIX_AxisWallAtlasFamily_measure_image_of_firstPieces
-- name    : BianchiIX.AxisWallAtlasFamily.measure_image_of_firstPieces
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T03:32:46.895408+00:00
-- url     : https://prove2.me/theorems/bb1adce9-2747-45c5-97d6-d6e850c52dbe
-- title:
--   Exact image measure after assembling the first-arrival pieces
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
--   Let the labels be encodable with measurable singletons, $h>0$, and let
--   the targets $E_i$ and time set $I$ be measurable. Suppose
--   $D\subset\bigcup_q L_q$ and $R:D\to\iota\times\mathbb R^3$ is the
--   restriction of a map injective on $D$. On every $L_q$, $q=(i,n)$,
--   the given total map agrees with $(i,R_q)$ and the given extended
--   nonnegative weight $j$ agrees with $(j_q)^+$. For every measurable
--   $S\subset D$, $R(S)$ is measurable and
--   $$\nu_k(R(S))=\int_S j\,d\mu_h.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/AxisReturnMeasure.lean#L38-L88

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
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
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry} {h t₀ : ℝ} {k : ι → ℝ}
  (C : AxisWallAtlasFamily A B h k t₀)

omit [Nonempty ι]

theorem BianchiIX.AxisWallAtlasFamily.measure_image_of_firstPieces {E : ι → Set SectionCoordinates} {D S : Set SectionCoordinates}
    {I : Set ℝ} {R : SectionCoordinates → ι × SectionCoordinates} {j : SectionCoordinates → ℝ≥0∞}
    (hh : 0 < h) (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I)
    (hcover : D ⊆ ⋃ q, C.firstPiece E I q) (hinj : InjOn R D)
    (hR : ∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q))
    (hj : ∀ q : ι × ℕ, EqOn j (fun y => ENNReal.ofReal (((C q.1).branch q.2).jacobian y)) (C.firstPiece E I q))
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ y in S, j y ∂mainWallMeasure h := by sorry
