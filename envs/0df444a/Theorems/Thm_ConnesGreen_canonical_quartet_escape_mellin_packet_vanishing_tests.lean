-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_escape_mellin_packet_vanishing_tests
-- name    : ConnesGreen.canonical_quartet_escape_mellin_packet_vanishing_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T14:02:53.749528+00:00
-- url     : https://prove2.me/theorems/82168485-f437-4fc0-bf44-3c3886d45b9b
-- title:
--   Escaping witnesses: vanishing weighted actual-quartet Mellin energy
-- statement:
--   For every actual off-critical-line critical-strip zeta zero, obtain the attained positive original quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. CONDITIONAL on right-support endpoint half-bound failure and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that for every ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original supported test g with multiplicity-weighted actual quartet Mellin energy sum_{τ∈quartet} m(τ)|mellinHat(g,τ)|²<ε. Its physical source norm squared is ONE in the fixed original carrier c+1. In that same carrier its selected quartet energy a satisfies 0<a<ε, its complete positive energy p satisfies 0≤p<ε, and restored Weil value Q=Re W(g*starInv g)+FULL actual unselected-negative background energy satisfies -ε<Q<-δa<0. The fixed δ precedes ε; radius precedes every window/test. Neither conditional antecedent is asserted unconditionally. The quartet is the existing finite set, with duplicates removed and actual analytic multiplicity weights retained. No new zero carrier, multiplicity-positivity assumption or four-distinct-zero assumption is introduced. Only the weighted energy is stated; no division by multiplicity is used. No background decay, actual kernel vector, unconditional neutral-shell control or RH is established.
-- source:
--   For every actual off-critical-line critical-strip zeta zero, obtain the attained positive original quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. CONDITIONAL on right-support endpoint half-bound failure and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that for every ε>0 there is r∈(0,1) and EVERY c<T<c+r admits an original supported test g with multiplicity-weighted actual quartet Mellin energy sum_{τ∈quartet} m(τ)|mellinHat(g,τ)|²<ε. Its physical source norm squared is ONE in the fixed original carrier c+1. In that same carrier its selected quartet energy a satisfies 0<a<ε, its complete positive energy p satisfies 0≤p<ε, and restored Weil value Q=Re W(g*starInv g)+FULL actual unselected-negative background energy satisfies -ε<Q<-δa<0. The fixed δ precedes ε; radius precedes every window/test. Neither conditional antecedent is asserted unconditionally. The quartet is the existing finite set, with duplicates removed and actual analytic multiplicity weights retained. No new zero carrier, multiplicity-positivity assumption or four-distinct-zero assumption is introduced. Only the weighted energy is stated; no division by multiplicity is used. No background decay, actual kernel vector, unconditional neutral-shell control or RH is established.
--
--   New generic reduction: exact finite-packet multiplicity-weighted Mellin energy ≤ twice the sum of full positive and selected original adjoint energies, on ANY finite actual-zero selection. New quartet consequence: the already certified physical-unit witnesses may simultaneously make their actual weighted quartet samples arbitrarily small. Complete background is retained in restored negativity; it is not asserted small separately.
--
--   Critical-window location, actual uniform arithmetic endpoint estimate and unconditional neutral-shell control remain open. Ordered-limit existence is previously certified without an exchange. Repository/source modules remain unchanged at ada7948cb459fd21d400cd8f2a92e87672e31f2d; new proofs are standalone outputs.

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

theorem ConnesGreen.canonical_quartet_escape_mellin_packet_vanishing_tests
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
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by sorry
