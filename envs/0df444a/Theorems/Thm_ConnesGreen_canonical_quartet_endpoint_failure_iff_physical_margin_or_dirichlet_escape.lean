-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_physical_margin_or_dirichlet_escape
-- name    : ConnesGreen.canonical_quartet_endpoint_failure_iff_physical_margin_or_dirichlet_escape
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T08:04:25.244452+00:00
-- url     : https://prove2.me/theorems/80527699-e1a3-4a92-9d0a-a0142345c883
-- title:
--   Endpoint failure: physical margin or uniform Dirichlet-energy escape
-- statement:
--   For every ACTUAL critical-strip zeta zero off the critical line, there is a positive attained original quartet cut c≥positiveSupportRadius, where the original inner half-bound holds precisely for positive windows T≤c. At that SAME cut, failure of the right-support endpoint half-bound is equivalent to the following inclusive alternative. First: a single ε>0 works for every c<T<c+1, with an original supported test of physical source energy one and Re W plus COMPLETE actual unselected-negative background energy below −ε. Second: there is ONE δ in (0,1) such that every positive T>c admits an original supported test of selected quartet energy exactly one and the restored Weil value below −δ; furthermore, for EVERY M>0 there is r in (0,1) such that EVERY c<T<c+r and EVERY original supported test satisfying those same unit-selected and −δ margin conditions has global Dirichlet energy strictly greater than M. The escape branch includes actual witness feasibility at every larger window. Neither endpoint failure nor either alternative is asserted unconditionally. The alternatives are joined by ordinary inclusive OR; no exclusivity is asserted.
-- source:
--   New closed consequence of four accepted actual-zero dependencies. At the attained original quartet cut, endpoint failure is equivalent to an inclusive alternative: a uniform full-background physical margin on unit physical tests near the cut, or one fixed normalized selected-energy margin feasible in every larger window for which ALL qualifying original tests exceed every Dirichlet energy cap throughout a sufficiently small right neighborhood. The escape branch explicitly includes witness existence, hence is not vacuous. Generic escape follows from absence of a physical margin, bounded-test equivalence, and exact original window/actor/restored energy custody. No compactness or limit exchange is assumed. Native sources unchanged; original RPB108 attachments remain future formalization. Neither actual endpoint failure nor either alternative is proved unconditionally.

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

theorem ConnesGreen.canonical_quartet_endpoint_failure_iff_physical_margin_or_dirichlet_escape
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        (∃ ε : ℝ, 0 < ε ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
              (weilDistribution (conv g (starInv g))).re +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) ∨
        (∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          (∀ T : ℝ, ∀ hT : 0 < T, c < T →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
              (weilDistribution (conv g (starInv g))).re +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) ∧
          (∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
            ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
              ∀ g : ℝ → ℂ, SupportedTest T g →
                ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
                (weilDistribution (conv g (starInv g))).re +
                  ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                    (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
                M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                  (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by sorry
