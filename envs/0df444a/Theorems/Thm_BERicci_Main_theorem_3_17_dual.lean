-- Prove2me | Theorems.Thm_BERicci_Main_theorem_3_17_dual
-- name    : BERicci.Main.theorem_3_17_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:05.495356+00:00
-- url     : https://prove2.me/theorems/4270482f-f569-453f-a5e7-9c6da9f44a77
-- title:
--   Theorem 3.17, p. 41 — dual flow exists and regularizes measures
-- statement:
--   Let $(X,m,\mathcal E)$ be a Riemannian energy measure space satisfying $(MD.exp)$ and $BE(K,\infty)$, and let $P_t$ be its heat flow. Then there is a dual semigroup $H_t$ on probability measures such that
--
--   $$H_t\mu\ll m\qquad(t>0,\;\mu\in\mathcal P(X)).$$
--
--   This is the absolute continuity assertion in the final paragraph of Theorem 3.17. It supplies the measure flow whose densities occur in the later entropy estimates.
-- source:
--   arXiv:1209.5786v4, Theorem 3.17, final assertions, p. 41

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Contract_Dual

namespace BERicci.Main

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- The dual-semigroup and absolute-continuity assertions in Theorem 3.17, p. 41. -/
theorem theorem_3_17_dual {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) [SigmaFinite m]
    (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hR : BERicci.Gamma.IsRiemannianEMS m E S) (hexp : BERicci.Gamma.MDexp m)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P)
    (K : ℝ) (hBE : BERicci.Gamma.BE m E P K 0) :
    ∃ H : ℝ → Measure X → Measure X,
      BERicci.Contract.IsDualSemigroup m P H ∧
      ∀ t : ℝ, 0 < t → ∀ μ : Measure X, IsProbabilityMeasure μ → H t μ ≪ m := by sorry

end BERicci.Main
