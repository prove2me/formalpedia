-- Prove2me | Theorems.Thm_BERicci_Main_theorem_4_17
-- name    : BERicci.Main.theorem_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:57.877336+00:00
-- url     : https://prove2.me/theorems/fe7462f0-753e-4220-b056-d210ca34ee80
-- title:
--   Theorem 4.17, p. 57 — $BE(K,\infty)$ implies $RCD(K,\infty)$
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be a Riemannian energy measure space whose intrinsic metric is complete and separable. If $(MD.exp)$ and $BE(K,\infty)$ hold for its heat flow, then
--
--   $$(X,d_{\mathcal E},m)\text{ is an }RCD(K,\infty)\text{ space}. $$
--
--   In particular, from every $\rho\in\mathcal P_2(X)$ there is a measure flow starting at $\rho$ that satisfies the $EVI_K$ inequality at every positive time against every finite-entropy comparison measure.
--
--   **Formalization Note** This is the forward implication proved by the paper. The converse is cited from [5], §6, and is not part of this goal. The Borel sigma algebra represents the completed sigma algebra because all relevant quantities are invariant under almost everywhere equality.
-- source:
--   arXiv:1209.5786v4, Theorem 4.17, p. 57; converse cited in proof, p. 58

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Main

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- The forward implication of Theorem 4.17, p. 57. -/
theorem theorem_4_17 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) [SigmaFinite m]
    (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hR : BERicci.Gamma.IsRiemannianEMS m E S) (hexp : BERicci.Gamma.MDexp m)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m E P)
    (K : ℝ) (hBE : BERicci.Gamma.BE m E P K 0) : BERicci.Gamma.IsRCDInfty m K := by sorry

end BERicci.Main
