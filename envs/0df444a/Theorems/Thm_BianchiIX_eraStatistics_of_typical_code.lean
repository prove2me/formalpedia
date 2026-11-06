-- Prove2me | Theorems.Thm_BianchiIX_eraStatistics_of_typical_code
-- name    : BianchiIX.eraStatistics_of_typical_code
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:11:29.623544+00:00
-- url     : https://prove2.me/theorems/630d1648-8b7b-4ac1-ba2e-a9314c03a0a3
-- title:
--   All era statistics from a cylinder-typical code
-- statement:
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
--   Suppose $\pi(a)\in\mathcal B_G$, $y_n\in[0,1]$,
--   and $|y_n-1/(a_n+y_{n+1})|\to0$. Then $\mathcal E(a,y)$ holds.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraStatistics.lean#L29-L40

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

theorem BianchiIX.eraStatistics_of_typical_code (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    {y : ℕ → ℝ} (hy : ∀ n, y n ∈ Icc (0 : ℝ) 1)
    (herror : Tendsto (inverseError (fun n => (a n : ℕ)) y) atTop (𝓝 0)) :
    EraStatistics a y := by sorry
