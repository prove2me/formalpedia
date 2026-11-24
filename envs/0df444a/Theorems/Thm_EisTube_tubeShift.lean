-- Prove2me | Theorems.Thm_EisTube_tubeShift
-- name    : EisTube.tubeShift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:27:01.101328+00:00
-- url     : https://prove2.me/theorems/8dccf2af-2170-444e-b57a-6a4bef3a2d91
-- title:
--   Eis Tube: tube Shift
-- statement:
--   The Eis Tube construction uses the tube Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/Lemmas.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/Lemmas.lean#L27-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomainStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftParametrisedIntegralStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open EisTube

theorem EisTube.tubeShift : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by sorry
