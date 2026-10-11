-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_escape_signed_packet_vanishing_tests
-- name    : ConnesGreen.canonical_quartet_escape_signed_packet_vanishing_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T14:30:08.19923+00:00
-- url     : https://prove2.me/theorems/344e9305-9bd6-4a3b-a704-c58e303049b6
-- title:
--   Escaping witnesses: vanishing absolute actual-quartet Weil zero terms
-- statement:
--   For every actual critical-strip zeta zero ρ off the critical line, there is an attained c>0 with c≥positiveSupportRadius such that the original quartet inner marker half-bound holds exactly for the positive windows T≤c. CONDITIONAL on failure of the original right-support half-bound at c and absence of a uniform negative restored-Weil margin for physical-unit original tests in c<T<c+1, there is one δ∈(0,1) such that for EVERY ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original SupportedTest T g with all the following simultaneously: multiplicity-weighted actual quartet Mellin energy <ε; the SUM OF ABSOLUTE VALUES of the actual quartet explicit-formula terms m(τ)*mellinHat(g*starInv g,τ) <ε; absolute real part of their finite sum <ε; physical source norm squared ONE in the same fixed original carrier c+1; selected energy a satisfies 0<a<ε, complete positive energy p satisfies 0≤p<ε, and restored Weil value Q=Re W(g*starInv g)+COMPLETE actual unselected-negative background energy satisfies -ε<Q<-δa<0 in that carrier. The fixed δ precedes ε, and radius precedes every window/test. Neither conditional antecedent is asserted. The quartet is the existing reflection/conjugation finite set of actual zeros with duplicate points removed and actual analytic multiplicities retained. No positive-multiplicity assumption, four-distinct-points assumption, or new zero carrier is introduced. No smallness or domination estimate for the infinite complement, separate background decay, actual limiting kernel vector, unconditional endpoint or neutral-shell control, ordered-limit exchange, or RH is concluded.
-- source:
--   For every actual critical-strip zeta zero ρ off the critical line, there is an attained c>0 with c≥positiveSupportRadius such that the original quartet inner marker half-bound holds exactly for the positive windows T≤c. CONDITIONAL on failure of the original right-support half-bound at c and absence of a uniform negative restored-Weil margin for physical-unit original tests in c<T<c+1, there is one δ∈(0,1) such that for EVERY ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original SupportedTest T g with all the following simultaneously: multiplicity-weighted actual quartet Mellin energy <ε; the SUM OF ABSOLUTE VALUES of the actual quartet explicit-formula terms m(τ)*mellinHat(g*starInv g,τ) <ε; absolute real part of their finite sum <ε; physical source norm squared ONE in the same fixed original carrier c+1; selected energy a satisfies 0<a<ε, complete positive energy p satisfies 0≤p<ε, and restored Weil value Q=Re W(g*starInv g)+COMPLETE actual unselected-negative background energy satisfies -ε<Q<-δa<0 in that carrier. The fixed δ precedes ε, and radius precedes every window/test. Neither conditional antecedent is asserted. The quartet is the existing reflection/conjugation finite set of actual zeros with duplicate points removed and actual analytic multiplicities retained. No positive-multiplicity assumption, four-distinct-points assumption, or new zero carrier is introduced. No smallness or domination estimate for the infinite complement, separate background decay, actual limiting kernel vector, unconditional endpoint or neutral-shell control, ordered-limit exchange, or RH is concluded.
--
--   The generic finite-packet bounds are unconditional for any IsTest g and reflection-closed finite selection of actual zeros. The witness theorem is conditional exactly as its accepted predecessor. All normalization uses existing multiplicity reflection and the accepted convolution transform. The two original developments and original theorem statements remain unchanged. New proof declarations are standalone outputs; repository head is ada7948cb459fd21d400cd8f2a92e87672e31f2d, with no new repository commit.

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

theorem ConnesGreen.canonical_quartet_escape_signed_packet_vanishing_tests
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
          (∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2) < ε ∧
          (∑ τ ∈ quartet ρ, ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε ∧
          |(∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by sorry
