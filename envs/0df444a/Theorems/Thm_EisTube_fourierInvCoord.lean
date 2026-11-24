-- Prove2me | Theorems.Thm_EisTube_fourierInvCoord
-- name    : EisTube.fourierInvCoord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:16:22.703827+00:00
-- url     : https://prove2.me/theorems/0ead3706-df56-47a9-9a4f-f1ea60410f56
-- title:
--   Eis Tube: fourier Inv Coord
-- statement:
--   The Eis Tube construction uses the fourier Inv Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/Lemmas.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/Lemmas.lean#L20-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDimStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomainStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftParametrisedIntegralStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_fourierInvCoord

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

theorem EisTube.fourierInvCoord : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y := by sorry
