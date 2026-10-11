-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_eventual_restored_arithmetic
-- name    : ConnesGreen.canonical_endpoint_half_iff_eventual_restored_arithmetic
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T18:42:08.486377+00:00
-- url     : https://prove2.me/theorems/c08d6b59-1e15-451c-8fa0-f2dd3f001cdb
-- title:
--   Original ordered endpoint half-bound is equivalent to eventual restored arithmetic control
-- statement:
--   # Exact ordered endpoint / eventual arithmetic equivalence
--
--   For every bounded support range T>0, fixed finite actual-zero selected packet S, finite requests K_n, and prescribed positive schedules μ_n→0 and 0<ε_n<1 with ε_n→0, there exists a nested reflection-closed finite restoration sequence F_n containing S and K_n. All preceding uniform actual-zero tails, strict positivity, marker-error bounds, fixed-window Picard convergence and prescribed ordered endpoint approximation are retained.
--
--   For every 0≤c<T, the original support-right marker satisfies (1/2)I≤Γ⁺_(c,S) if and only if, for every 0<η<1/2, there is d>0 with c+d≤T such that, for every c<t<c+d, eventually in n every original supported test g satisfies
--
--   E_(S,t)(g) ≤ ((1/2−η)⁻¹−1) · (Re W(g*starInv(g)) + E_(F_n,t)(g) + μ_n D(g)).
--
--   Here E_(A,t)(g)=‖N_(t,A)* sourceEmbed(t,problemOneL(g))‖² uses the original negative synthesis actor on actual zeta zeros, and D(g)=∫‖g′‖²+(1/4)∫‖g‖². The coefficient multiplies the entire parenthesis. The selected actor is S throughout; F_n only restores omitted negative directions. There is no norm restriction on g in this equivalence.
--
--   The radius d is chosen before t; the eventual stage N is chosen after t and before g. No common N over nearby windows, exchange of limits, exhaustion of all zeros, or effective cutoff is asserted. This theorem identifies the remaining arithmetic obstruction; it does not establish either side of the equivalence unconditionally or establish RH.
-- source:
--   # Certified reduction; arithmetic estimate remains open
--
--   For every bounded support range T>0, fixed finite actual-zero selected packet S, finite requests K_n, and prescribed positive schedules μ_n→0 and 0<ε_n<1 with ε_n→0, there exists a nested reflection-closed finite restoration sequence F_n containing S and K_n. All preceding uniform actual-zero tails, strict positivity, marker-error bounds, fixed-window Picard convergence and prescribed ordered endpoint approximation are retained.
--
--   For every 0≤c<T, the original support-right marker satisfies (1/2)I≤Γ⁺_(c,S) if and only if, for every 0<η<1/2, there is d>0 with c+d≤T such that, for every c<t<c+d, eventually in n every original supported test g satisfies
--
--   E_(S,t)(g) ≤ ((1/2−η)⁻¹−1) · (Re W(g*starInv(g)) + E_(F_n,t)(g) + μ_n D(g)).
--
--   Here E_(A,t)(g)=‖N_(t,A)* sourceEmbed(t,problemOneL(g))‖² uses the original negative synthesis actor on actual zeta zeros, and D(g)=∫‖g′‖²+(1/4)∫‖g‖². The coefficient multiplies the entire parenthesis. The selected actor is S throughout; F_n only restores omitted negative directions. There is no norm restriction on g in this equivalence.
--
--   The radius d is chosen before t; the eventual stage N is chosen after t and before g. No common N over nearby windows, exchange of limits, exhaustion of all zeros, or effective cutoff is asserted. This theorem identifies the remaining arithmetic obstruction; it does not establish either side of the equivalence unconditionally or establish RH.
--
--   The accepted restored ordered-endpoint theorem supplies the same nested sequence and every preceding estimate. Its strict-positive restored covariances imply self-adjoint restored markers. A norm-close self-adjoint operator loses at most η of a scalar lower bound. This transports the endpoint half-bound to eventual finite-stage bounds (1/2−η)I.
--
--   Conversely, take η=min(ζ/2,1/4) for any ζ>0. Choose one positive window inside the supplied interval, pass its eventual bound through the fixed-window norm limit using the closed positive cone, and use the original least-upper-bound specification to compare that Picard marker to the support-right marker. Closing all positive scalar slacks yields the endpoint half-bound.
--
--   Finally, the independently accepted canonical_finite_marker_lower_iff_arithmetic_tests applies with β=1/2−η and regularization μ_n. This converts every stage bound exactly to the stated original-test inequality. No desired inequality is a hypothesis of the primary theorem. Numeric schedule assumptions are explicit. Generic convergence assumptions in the intermediate helper are discharged by the accepted predecessor.
--
--   The native proof is a standalone closed assembly over the existing certified module closure, with only standard Lean axioms. The platform proof imports exactly the two accepted dependencies listed in fragments.json. No source theorem is weakened or rewritten. Failed first-attempt logs are retained as diagnostics, not validation. Publication, exact readback and mission linkage are recorded separately.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_iff_eventual_restored_arithmetic
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T → ∀ δ : ℝ, 0 < δ →
        ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by sorry
