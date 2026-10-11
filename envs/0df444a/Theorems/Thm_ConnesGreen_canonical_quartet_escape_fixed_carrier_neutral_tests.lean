-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_escape_fixed_carrier_neutral_tests
-- name    : ConnesGreen.canonical_quartet_escape_fixed_carrier_neutral_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T13:40:23.020991+00:00
-- url     : https://prove2.me/theorems/bec3f7ce-1ef1-4154-b3a1-80116b8dc279
-- title:
--   Escaping witnesses: small positive and selected energy in a fixed carrier
-- statement:
--   For every actual off-critical-line critical-strip zeta zero, obtain the attained positive original quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. CONDITIONAL on failure of the right-support endpoint half-bound and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that for each ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original test g supported in (-T,T), whose physical source norm squared is ONE in the fixed original carrier at c+1. In that SAME fixed carrier its selected quartet energy a satisfies 0<a<ε, its full positive actor energy p satisfies 0≤p<ε, and its complete restored Weil value Q=Re W(g*starInv g)+the FULL actual unselected-negative background energy satisfies -ε<Q<-δ a<0. δ is fixed before ε; r may depend on ε; the test may depend on T. This produces arbitrarily small joint positive/selected actor energies on physical-unit original tests in a single carrier, not an actual joint-kernel vector or unconditional neutral-shell control. Endpoint failure and absence of a physical margin are NOT established. No separate smallness of background energy or Re W is asserted. RH remains open.
-- source:
--   For every actual off-critical-line critical-strip zeta zero, obtain the attained positive original quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. CONDITIONAL on failure of the right-support endpoint half-bound and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that for each ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original test g supported in (-T,T), whose physical source norm squared is ONE in the fixed original carrier at c+1. In that SAME fixed carrier its selected quartet energy a satisfies 0<a<ε, its full positive actor energy p satisfies 0≤p<ε, and its complete restored Weil value Q=Re W(g*starInv g)+the FULL actual unselected-negative background energy satisfies -ε<Q<-δ a<0. δ is fixed before ε; r may depend on ε; the test may depend on T. This produces arbitrarily small joint positive/selected actor energies on physical-unit original tests in a single carrier, not an actual joint-kernel vector or unconditional neutral-shell control. Endpoint failure and absence of a physical margin are NOT established. No separate smallness of background energy or Re W is asserted. RH remains open.
--
--   New construction: physical normalization of escaping original witnesses in the fixed carrier c+1, simultaneous smallness of the complete positive and selected actual-zero actors, and strict full-background restored-Weil negativity squeezed to zero. This is an approximate joint-kernel family with original test/source custody; it does not produce a neutral-shell vector or rule out its existence.
--
--   Critical-window location, concrete arithmetic endpoint control and unconditional neutral-shell control remain open. Ordered-limit existence was previously certified, without exchange. Repository/source modules remain unchanged at ada7948cb459fd21d400cd8f2a92e87672e31f2d; new declarations are standalone output proofs.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_quartet_escape_fixed_carrier_neutral_tests
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
((¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ)) → ¬ (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) →
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by sorry
