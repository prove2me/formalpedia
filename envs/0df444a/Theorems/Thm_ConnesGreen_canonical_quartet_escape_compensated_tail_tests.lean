-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_escape_compensated_tail_tests
-- name    : ConnesGreen.canonical_quartet_escape_compensated_tail_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T14:46:20.997455+00:00
-- url     : https://prove2.me/theorems/41856c2b-5b5e-449e-a27e-f2819f929e94
-- title:
--   Escaping witnesses: exact actual complement and vanishing compensated real tail
-- statement:
--   For each ACTUAL critical-strip zeta zero ρ off the critical line, obtain an attained c>0, c≥positiveSupportRadius, with the original quartet inner half-bound exactly for positive windows T≤c. CONDITIONAL on right-support endpoint half-bound failure and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that EVERY ε>0 admits r∈(0,1) and EVERY c<T<c+r admits a SAME original SupportedTest T g with all preceding guarantees: weighted quartet Mellin energy <ε, sum of absolute ACTUAL convolved quartet zero terms <ε, absolute real quartet contribution <ε, physical norm squared ONE in original fixed carrier c+1, 0<a<ε for selected energy, 0≤p<ε for complete positive energy, and -ε<Q<-δa<0 for Q=Re W(g*starInv g)+FULL actual unselected-negative background b in that carrier. In addition the COMPLETE actual complement (all critical-strip zeros outside this quartet, with actual multiplicities) has HasSum limit W(g*starInv g) minus the finite actual quartet sum, and its series of term norms is summable. Its REAL signed sum L satisfies |L+b|<ε, with b the SAME complete background energy in c+1. δ is fixed before ε, radius before every window/test. Neither conditional hypothesis is asserted. Quartet duplicates are removed as finite-set entries; no distinctness or multiplicity-positivity premise is added. This is a bound on the COMPENSATED REAL complement, not an ε-bound on the norm sum, uncompensated tail or b. No prescribed limiting vector, separate background decay, uniform arithmetic endpoint estimate, unconditional endpoint or neutral-shell control, ordered-limit exchange or RH is proved.
-- source:
--   For each ACTUAL critical-strip zeta zero ρ off the critical line, obtain an attained c>0, c≥positiveSupportRadius, with the original quartet inner half-bound exactly for positive windows T≤c. CONDITIONAL on right-support endpoint half-bound failure and absence of a uniform restored-Weil negative margin on physical-unit original tests near c, there is one δ∈(0,1) such that EVERY ε>0 admits r∈(0,1) and EVERY c<T<c+r admits a SAME original SupportedTest T g with all preceding guarantees: weighted quartet Mellin energy <ε, sum of absolute ACTUAL convolved quartet zero terms <ε, absolute real quartet contribution <ε, physical norm squared ONE in original fixed carrier c+1, 0<a<ε for selected energy, 0≤p<ε for complete positive energy, and -ε<Q<-δa<0 for Q=Re W(g*starInv g)+FULL actual unselected-negative background b in that carrier. In addition the COMPLETE actual complement (all critical-strip zeros outside this quartet, with actual multiplicities) has HasSum limit W(g*starInv g) minus the finite actual quartet sum, and its series of term norms is summable. Its REAL signed sum L satisfies |L+b|<ε, with b the SAME complete background energy in c+1. δ is fixed before ε, radius before every window/test. Neither conditional hypothesis is asserted. Quartet duplicates are removed as finite-set entries; no distinctness or multiplicity-positivity premise is added. This is a bound on the COMPENSATED REAL complement, not an ε-bound on the norm sum, uncompensated tail or b. No prescribed limiting vector, separate background decay, uniform arithmetic endpoint estimate, unconditional endpoint or neutral-shell control, ordered-limit exchange or RH is proved.
--
--   The unconditional generic complement HasSum, absolute summability and restoration-balance lemmas use the independently certified actual-zeta explicit formula and a closed test-class convolution proof. They require only IsTest g and any finite actual-zero selection S, with no reflection-closure hypothesis. The attained-cut witness consequence retains both original conditional antecedents. Repository head remains ada7948cb459fd21d400cd8f2a92e87672e31f2d; output proofs are standalone, no new repository commit. Original RPB108 original-form attachments remain a clearly identified future formalization task.

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

theorem ConnesGreen.canonical_quartet_escape_compensated_tail_tests
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
          HasSum (fun τ : CriticalZeros => if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)
            (weilDistribution (conv g (starInv g)) -
              ∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) ∧
          Summable (fun τ : CriticalZeros => ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
          |(∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re +
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by sorry
