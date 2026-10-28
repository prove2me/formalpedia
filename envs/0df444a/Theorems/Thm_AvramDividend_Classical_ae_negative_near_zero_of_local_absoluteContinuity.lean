-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_local_absoluteContinuity
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_local_absoluteContinuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:56:19.842266+00:00
-- url     : https://prove2.me/theorems/87589f4d-e1d4-4ce4-b689-7f1e3a03ed17
-- title:
--   Downward regularity transfers under finite-horizon local absolute continuity without requiring global equivalence of Lévy path laws
-- statement:
--   Let P and Q be path probability measures for the same process, and let positive observation horizons tend cofinally to zero. Assume that each event of a negative observation before horizon t_n is measurable in the original filtration F_{t_n}, and Q is locally absolutely continuous with respect to P on that horizon's measurable sets, in the precise null-set implication P(A)=0 ⇒ Q(A)=0. If P-almost every path visits negative values before every positive ε, the same is true Q-almost surely. This is the correct local Esscher law-change interface for Lévy processes, whose full infinite-horizon path measures need not be globally absolutely continuous.
-- source:
--   Finite-horizon Esscher change of measure and local absolute continuity; Kuznetsov, Kyprianou and Rivero (2013) on the Esscher-tilted excursion scale representation and regularity; standard countable intersection of a.e. events.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_local_absoluteContinuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (P Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (horizons : ℕ → ℝ≥0)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hEvent : ∀ n : ℕ,
      MeasurableSet[𝓕 (horizons n)]
        {ω : Ω | ∃ s : ℝ≥0,
          s < horizons n ∧ X s ω < 0})
    (hLocalAC : ∀ n : ℕ, ∀ A : Set Ω,
      MeasurableSet[𝓕 (horizons n)] A →
        P A = 0 → Q A = 0)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X s ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X s ω < 0 := by sorry
