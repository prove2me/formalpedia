-- Prove2me | Theorems.Thm_AnalyticOn_norm_le_of_norm_le_on_sphere
-- name    : AnalyticOn.norm_le_of_norm_le_on_sphere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:25:43.119827+00:00
-- url     : https://prove2.me/theorems/ac0e10ec-2cf2-4a3f-ad66-b0ab93c5020d
-- title:
--   Maximum modulus bound on a disk from a bound on an interior circle
-- statement:
--   Let $C, r, R \in \mathbb{R}$ with $r \le R$, let $f : \mathbb{C} \to \mathbb{C}$ be analytic on the closed disk $\overline{D}(0,R) = \{z : \|z\| \le R\}$ (in the sense of Mathlib's `AnalyticOn`), and suppose that $\|f(z)\| \le C$ for every $z$ on the circle $\{z : \|z\| = r\}$.
--
--   Then for every point $w$ in the closed disk $\overline{D}(0,r)$,
--   $$\|f(w)\| \le C.$$
--
--   This is an instance of the maximum modulus principle: a bound for an analytic function on a circle propagates to the whole closed disk it bounds. In the project it lives in the preparatory module `Zeta23.FromPNTPlus.StrongPNTPrefix` and is used in the proof of the Jensen-type zero-counting bound `ZerosBound` and in the estimate `Zeta23.WeilEF.norm_logDeriv_Cf_le` bounding the logarithmic derivative of the zero-free factor $C_f$, both ingredients of the Weil explicit-formula side of the argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean#L33-L49

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

theorem AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by sorry
