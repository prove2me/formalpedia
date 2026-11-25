-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_landau_ord_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_landau_ord_core
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:03.830635+00:00
-- url     : https://prove2.me/theorems/b84de459-18dd-499a-aeed-bfafb48bfeb0
-- title:
--   Primes In Progressions: ex landau ord core
-- statement:
--   The Primes In Progressions construction uses the ex landau ord core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLoc.lean#L115-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLoc.lean#L115-L299

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
open Filter Topology Metric

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_landau_ord_core (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 1 ≤ B)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log B / r := by sorry
