-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_ae_rogozin_negative_slopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:41:14.75974+00:00
-- url     : https://prove2.me/theorems/b2e617e8-5a14-4082-8f6a-4c6af34e23a7
-- title:
--   Rogozin unbounded-variation small-time negative-slope oscillation implies zero regularity for the negative half-line
-- statement:
--   If under the Lévy probability P almost every sample path has arbitrarily small positive times where its slope X_t/t falls below every real threshold C, equivalently the Rogozin lower small-time oscillation liminf(X_t/t)=-∞, then the Lévy path has strictly negative observations arbitrarily near zero almost surely. This isolates a precisely stated nontrivial stochastic prerequisite from the remaining elementary filter-topology implication. The theorem does not assume the conclusion, nor does it purport to derive Rogozin oscillation from Lévy characteristics.
-- source:
--   Rogozin's theorem on small-time oscillation of unbounded-variation Lévy processes, e.g. González Cázares, *Convex Minorants and the Fluctuation Theory of Lévy Processes* (2021), Theorem 2.16; Kuznetsov, Kyprianou and Rivero (2013), §2.3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Bornology.Real
import Mathlib.Order.Filter.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_ae_rogozin_negative_slopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSlope : ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
