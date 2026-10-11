-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_escape_negative_ray_tests
-- name    : ConnesGreen.canonical_quartet_escape_negative_ray_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T16:49:19.895983+00:00
-- url     : https://prove2.me/theorems/bf4ec6bd-c297-4e00-a234-c5d85d31a8f6
-- title:
--   Escaping witnesses: complete actual tail approaches the negative real ray
-- statement:
--   For every actual critical-strip zeta zero ρ off the critical line, recover the SAME attained positive cut c≥positiveSupportRadius, with the original quartet inner half-bound iff 0<T≤c. CONDITIONAL on failure of the original right-support half-bound at c AND absence of a uniform restored-Weil negative margin on original physical-unit tests for c<T<c+1, there is one δ∈(0,1), fixed before every ε>0, such that some r∈(0,1) works for EVERY c<T<c+r. One SAME original SupportedTest T g has all preceding guarantees in the original fixed carrier c+1: weighted quartet Mellin energy, absolute quartet actual zero contribution, absolute real quartet contribution, selected energy a and complete positive energy p are <ε; a>0; physical norm squared is ONE; -ε<Q<-δa<0 for Q=Re W(g*starInv g)+b with b the COMPLETE actual unselected-negative background energy. The complete actual complement f(τ), zero on the quartet and otherwise actual multiplicity times the convolved Mellin transform at the actual zero, has HasSum W minus the quartet sum and summable term norms. With N=Σ‖f(τ)‖ and L=Re Σ f(τ), both |L+b|<ε and |N-b|<ε remain true. ADDITIONALLY, the sum of the nonnegative deviations ‖f(τ)+(‖f(τ)‖:ℂ)‖ is summable and <ε; the sum of |Im f(τ)| is summable and <ε; and the COMPLEX compensated tail satisfies ‖Σ f(τ)+(b:ℂ)‖<ε. Quartet repetitions are removed by its finite-set definition, retaining actual multiplicities. Neither conditional antecedent is asserted. No separate tail/background decay, prescribed limiting vector, arithmetic endpoint estimate, unconditional neutral-shell control, ordered-limit exchange, or RH is proved.
-- source:
--   For every actual critical-strip zeta zero ρ off the critical line, recover the SAME attained positive cut c≥positiveSupportRadius, with the original quartet inner half-bound iff 0<T≤c. CONDITIONAL on failure of the original right-support half-bound at c AND absence of a uniform restored-Weil negative margin on original physical-unit tests for c<T<c+1, there is one δ∈(0,1), fixed before every ε>0, such that some r∈(0,1) works for EVERY c<T<c+r. One SAME original SupportedTest T g has all preceding guarantees in the original fixed carrier c+1: weighted quartet Mellin energy, absolute quartet actual zero contribution, absolute real quartet contribution, selected energy a and complete positive energy p are <ε; a>0; physical norm squared is ONE; -ε<Q<-δa<0 for Q=Re W(g*starInv g)+b with b the COMPLETE actual unselected-negative background energy. The complete actual complement f(τ), zero on the quartet and otherwise actual multiplicity times the convolved Mellin transform at the actual zero, has HasSum W minus the quartet sum and summable term norms. With N=Σ‖f(τ)‖ and L=Re Σ f(τ), both |L+b|<ε and |N-b|<ε remain true. ADDITIONALLY, the sum of the nonnegative deviations ‖f(τ)+(‖f(τ)‖:ℂ)‖ is summable and <ε; the sum of |Im f(τ)| is summable and <ε; and the COMPLEX compensated tail satisfies ‖Σ f(τ)+(b:ℂ)‖<ε. Quartet repetitions are removed by its finite-set definition, retaining actual multiplicities. Neither conditional antecedent is asserted. No separate tail/background decay, prescribed limiting vector, arithmetic endpoint estimate, unconditional neutral-shell control, ordered-limit exchange, or RH is proved.
--
--   Native checkout head remains ada7948cb459fd21d400cd8f2a92e87672e31f2d. This standalone extension has no new repository commit. Local checks cover the complete native assembly and platform proof, rather than a new CI head. Original RPB108 original-form attachments remain a future formalization task.

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

theorem ConnesGreen.canonical_quartet_escape_negative_ray_tests
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
          |(∑' τ : CriticalZeros, ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) -
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          Summable (fun τ : CriticalZeros => ‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) + (‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ : ℂ)‖) ∧
          (∑' τ : CriticalZeros, ‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) + (‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ : ℂ)‖) < ε ∧
          Summable (fun τ : CriticalZeros => |(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).im|) ∧
          (∑' τ : CriticalZeros, |(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).im|) < ε ∧
          ‖(∑' τ : CriticalZeros, (if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)) + (‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 : ℂ)‖ < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by sorry
