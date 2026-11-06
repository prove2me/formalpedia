-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_typicalSurvivors_era_bounds
-- name    : BianchiIX.InverseBranchTree.BranchEstimates.typicalSurvivors_era_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:17:43.19981+00:00
-- url     : https://prove2.me/theorems/1c322eda-9abf-431c-a1d5-0942533f3df3
-- title:
--   Mass, restricted losses, and statistics of the typical survivor set
-- statement:
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--
--   Assume $R,U_{v,a}\subset(0,1)$ and that every branch is differentiable
--   with nonzero derivative on its domain. Let real sequences $d,e$ satisfy,
--   for every $t\in U_{v,a}$,
--   $$|h_{v,a}(t)-g_a(t)|\leq d_{|v|},\qquad
--   \left|\log\frac{|h_{v,a}'(t)|}{|g_a'(t)|}\right|\leq e_{|v|}.$$
--   Put $B_n=\sum_{j=0}^{n-1}e_j+2\sum_{j=1}^{n-1}d_j$, with empty sums zero,
--   and write $\lambda$ for Lebesgue measure.
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--
--   Assume $0<B\leq1$, $0\leq\eta\leq1/2$, $B^\eta<1/160$, and
--   $C_v,C_i\geq0$. Use the error sequences
--   $$d_m=C_vM_m(B),\qquad e_m=C_i\sqrt{M_m(B)},$$
--   and put $L_B=2C_i\sqrt B+4C_vB^{4/3}$.
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--
--   For $x\in S$, let $\phi_n(x)$ be the unique point of $K_{v_n(x)}$
--   with $H_{v_n(x)}(\phi_n(x))=x$.
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $G(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $G(0)=0$.
--   For a finite word $w=(a_0,\ldots,a_{k-1})$ of natural numbers, set
--   $$C_w=(g_{a_0}\circ\cdots\circ g_{a_{k-1}})((0,1)),\qquad
--   g_a(t)=1/(a+t),$$
--   where the empty composition is the identity and $0^{-1}=0$. Define
--   $$f_w=\mathbf1_{C_w},\qquad m_w=\mu_G(C_w),\qquad
--   \mathcal B_G=\left\{x\in\mathbb R:\ \forall w,\
--   \frac1n\sum_{j=0}^{n-1}f_w(G^jx)\longrightarrow m_w\right\}.$$
--   For a positive-digit sequence $a$, write $\pi(a)$ for its continued-fraction
--   code, $\sigma^j a$ for its tail beginning at $j$, and $a|_k$ for its first
--   $k$ digits.
--
--   Define $S_{\mathrm{typ}}=\{x\in S:\kappa(x)\in\mathcal B_G\}$,
--   regarded as a subset of $\mathbb R$.
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $G(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $G(0)=0$.
--   For a finite word $w=(a_0,\ldots,a_{k-1})$ of natural numbers, set
--   $$C_w=(g_{a_0}\circ\cdots\circ g_{a_{k-1}})((0,1)),\qquad
--   g_a(t)=1/(a+t),$$
--   where the empty composition is the identity and $0^{-1}=0$. Define
--   $$f_w=\mathbf1_{C_w},\qquad m_w=\mu_G(C_w),\qquad
--   \mathcal B_G=\left\{x\in\mathbb R:\ \forall w,\
--   \frac1n\sum_{j=0}^{n-1}f_w(G^jx)\longrightarrow m_w\right\}.$$
--   For a positive-digit sequence $a$, write $\pi(a)$ for its continued-fraction
--   code, $\sigma^j a$ for its tail beginning at $j$, and $a|_k$ for its first
--   $k$ digits.
--
--   Define the natural-valued digit, tail observables, and truncations by
--   $$D(x)=\lfloor1/x\rfloor_{\mathbb N},\qquad
--   H_k(x)=\mathbf1_{(0,1/k)}(x)\quad(k\geq1),\qquad
--   D_R(x)=\min(D(x),R)\quad(R\in\mathbb N).$$
--   Here the natural floor is zero for negative arguments, and $0^{-1}=0$.
--   Write
--   $$p_k=\frac{\log((k+1)^2/(k(k+2)))}{\log2},\qquad
--   q_k=\frac{\log(1+1/k)}{\log2},\qquad
--   t_R=\frac{\log(R+1)}{\log2}.$$
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   For a positive-digit sequence $a$ and a real sequence $y$, let
--   $\mathcal E(a,y)$ mean all of the following statements:
--   $$A_N(f\circ y)\to\int f\,d\mu_G
--   \quad\text{for every }f:\mathbb R\to\mathbb R
--   \text{ continuous on }[0,1],$$
--   $$A_N(j\mapsto\mathbf1_{\{(\sigma^ja)|_{|w|}=w\}})\to m_w
--   \quad\text{for every finite positive-digit word }w,$$
--   $$A_N(j\mapsto\mathbf1_{\{a_j=k\}})\to p_k,\qquad
--   A_N(j\mapsto\mathbf1_{\{k\leq a_j\}})\to q_k\quad(k\geq1),$$
--   $$A_N(j\mapsto\min(a_j,R))\to t_R\quad(R\in\mathbb N),\qquad
--   A_N(j\mapsto a_j)\to+\infty.$$
--   For a measurable space $X$, let $(\mathrm B)_X$ be
--   the following proposition: for every probability measure $\mu$ on $X$,
--   every ergodic map $F:X\to X$, and every integrable $f:X\to\mathbb R$,
--   $$\frac1n\sum_{j=0}^{n-1}f(F^jx)\longrightarrow\int_X f\,d\mu
--   \quad\text{for }\mu\text{-almost every }x.$$
--   This proposition is an explicit hypothesis in the results that use it.
--
--   Assume $(\mathrm B)_{\mathbb R}$, $R=(0,1)$, $L_B\leq\log2$, and
--   $\lambda(D_v)\leq10M_{|v|}(B)^\eta$ for all $v$. Then
--   $$\lambda(S_{\mathrm{typ}})>\tfrac12,\qquad
--   \lambda((I\cap R)\setminus(I\cap S_{\mathrm{typ}}))
--   \leq\min(\lambda(I),80B^\eta)\quad\text{for every }I,$$
--   and every $x\in S_{\mathrm{typ}}$ satisfies $\mathcal E(a(x),\phi(x))$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraBudget.lean#L164-L207

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates

theorem BianchiIX.InverseBranchTree.BranchEstimates.typicalSurvivors_era_bounds {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (hroot : T.root = Ioo (0 : ℝ) 1)
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η)) :
    (1 / 2 : ℝ≥0∞) < volume T.typicalSurvivors ∧
      (∀ I : Set ℝ, volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) ≤
        min (volume I) (ENNReal.ofReal (80 * B ^ η))) ∧
      ∀ x : T.survivors, x.val ∈ T.typicalSurvivors → EraStatistics (T.digits x) (T.phase x) := by sorry
