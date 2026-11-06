-- Prove2me | Theorems.Thm_BianchiIX_gaussEmpiricalMass_tendsto
-- name    : BianchiIX.gaussEmpiricalMass_tendsto
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:15:25.724529+00:00
-- url     : https://prove2.me/theorems/3da627bc-2bfb-430a-8180-a5aee282c022
-- title:
--   Coordinatewise convergence of empirical Gauss partition masses
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
--   Let $W_n$ be the set of positive-digit words of length $n$, including
--   the empty word for $n=0$. Put $m_n(w)=\mu_G(C_w)$. For a positive-digit
--   sequence $a$, define
--   $$p^a_{n,N}(w)=\frac1{N+1}\sum_{j=0}^N
--   \mathbf1_{\{(\sigma^ja)|_n=w\}}.$$
--
--   If $\pi(a)\in\mathcal B_G$, then for every $n$ and $w\in W_n$,
--   $$p^a_{n,N}(w)\longrightarrow m_n(w)\quad(N\to\infty).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussPartition.lean#L74-L78

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussPartition
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section

theorem BianchiIX.gaussEmpiricalMass_tendsto (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (n : ℕ) (w : GaussWords n) :
    Tendsto (fun N => gaussEmpiricalMass a n N w) atTop (𝓝 (gaussMass n w)) := by sorry
