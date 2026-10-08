-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_exists_original_neutral_window_inclusion
-- name    : ConnesGreen.RG0Integration.exists_original_neutral_window_inclusion
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:02:33.704394+00:00
-- url     : https://prove2.me/theorems/cc4e9645-08ce-438b-8807-d12e93b757cf
-- title:
--   Constructed original window inclusion preserves the neutral kernel under stated larger positivity
-- statement:
--   For positive nested original windows and the unchanged selected actual-zero packet, if the larger original signed covariance is nonnegative, there exists an original physical isometric inclusion preserving every supported-test source representative and carrying its neutral kernel exactly to the larger neutral kernel. The accepted window inclusion and exact original source-column compression construct the inclusion and actor custody; the accepted signed compression and nonnegative-kernel theorem prove the equivalence. Larger-window positivity is explicit. No neutral attainment at the critical endpoint or unconditional persistence there is asserted.
-- source:
--   WeilDefect/Connes/RG0DependencyIntegration.lean; CanonicalGreenNeutralShell.lean native original window custody, unchanged actual zeros and selected packet.

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_original_neutral_kernel_persists_of_source_compression
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.RG0Integration.exists_original_neutral_window_inclusion
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros)
    (hpos : 0 ≤ canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      (∀ x : Physical t,
        (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
          (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
        (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
          (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0) := by sorry
