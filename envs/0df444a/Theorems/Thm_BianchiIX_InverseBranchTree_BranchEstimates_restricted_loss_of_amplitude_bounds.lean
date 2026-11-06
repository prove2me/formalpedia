-- Prove2me | Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_restricted_loss_of_amplitude_bounds
-- name    : BianchiIX.InverseBranchTree.BranchEstimates.restricted_loss_of_amplitude_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:16:19.917446+00:00
-- url     : https://prove2.me/theorems/7caa7474-0da5-4aa1-be62-8f239556ac3f
-- title:
--   A uniform restricted loss bound from amplitude estimates
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
--   Assume also $L_B\leq\log2$ and
--   $\lambda(D_v)\leq10M_{|v|}(B)^\eta$ for every word $v$.
--   Then for every set $I\subset\mathbb R$,
--   $$\lambda((I\cap R)\setminus(I\cap S))
--   \leq\min(\lambda(I),80B^\eta).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraBudget.lean#L131-L152

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
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

theorem BianchiIX.InverseBranchTree.BranchEstimates.restricted_loss_of_amplitude_bounds {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η))
    (I : Set ℝ) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤ min (volume I) (ENNReal.ofReal (80 * B ^ η)) := by sorry
