-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape
-- name    : ConnesGreen.canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T08:14:49.422163+00:00
-- url     : https://prove2.me/theorems/e2d9bbaf-9964-496d-bf16-3492d0fcc61f
-- title:
--   Endpoint failure: physical margin or all-margin Dirichlet escape
-- statement:
--   For each actual critical-strip zeta zero off the critical line, there is the same positive attained quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. At that cut, endpoint failure is equivalent to either a uniform negative restored-Weil margin on physical-unit original tests in every c<T<c+1, or BOTH a fixed selected-unit negative margin feasible in every T>c and uniform Dirichlet-energy escape for EVERY selected-unit margin δ∈(0,1). For every such δ and every cap M>0 there is r∈(0,1) so every qualifying original test in every c<T<c+r has energy above M. The radius may depend on δ and M. Feasibility is asserted for one common δ only, not for every δ. The alternatives are logically disjoint by the separately proved generic equivalence between no physical margin and all-margin escape. Neither endpoint failure nor either alternative is proved to occur. RH remains open.
-- source:
--   For each actual critical-strip zeta zero off the critical line, there is the same positive attained quartet cut c≥positiveSupportRadius with the original inner half-bound iff T≤c. At that cut, endpoint failure is equivalent to either a uniform negative restored-Weil margin on physical-unit original tests in every c<T<c+1, or BOTH a fixed selected-unit negative margin feasible in every T>c and uniform Dirichlet-energy escape for EVERY selected-unit margin δ∈(0,1). For every such δ and every cap M>0 there is r∈(0,1) so every qualifying original test in every c<T<c+r has energy above M. The radius may depend on δ and M. Feasibility is asserted for one common δ only, not for every δ. The alternatives are logically disjoint by the separately proved generic equivalence between no physical margin and all-margin escape. Neither endpoint failure nor either alternative is proved to occur. RH remains open.
--
--   Closed new obstruction: absence of uniform physical margin iff ALL-margin uniform energy escape. This local equivalence makes the refined quartet alternatives mutually exclusive. The generic assertion can be vacuous for infeasible margins; the quartet branch separately requires feasibility at one margin in every larger window.
--
--   Critical-window location, concrete uniform arithmetic endpoint and unconditional neutral-shell control remain open. Ordered-limit existence is already certified, without an exchange. Sources and repository head ada7948cb459fd21d400cd8f2a92e87672e31f2d remain unchanged; new theorems are standalone output proofs.

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

theorem ConnesGreen.canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape
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
        ((∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) ∧ (∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
          ∀ g : ℝ → ℂ, SupportedTest T g →
            ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
            (weilDistribution (conv g (starInv g))).re +
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
            M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
              (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by sorry
