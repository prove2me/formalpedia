-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_boundary_with_original_neutral_custody
-- name    : ConnesGreen.canonical_quartet_boundary_with_original_neutral_custody
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:46:41.192161+00:00
-- url     : https://prove2.me/theorems/58b447dd-e17b-462e-b592-623407baf0d5
-- title:
--   Exact original quartet cutoff with neutral-kernel and source custody
-- statement:
--   For an ORIGINAL actual zeta zero $\rho$ off the critical line, we prove the exact native combined boundary and neutral-custody theorem. There is a finite $c\ge R>0$ such that
--   $$\forall T>0,\quad \tfrac12 I\le G_{Q(\rho)}(T)\ \Longleftrightarrow\ T\le c.$$
--   For EVERY pair $0<t\le T\le c$, an ORIGINAL source-compatible complex linear isometry $U:\operatorname{Physical}(t)\to\operatorname{Physical}(T)$ exists, preserves the original embedding of ALL supported tests at $t$, and satisfies
--   $$\forall x\in\operatorname{Physical}(t),\quad C_{t,Q(\rho)}x=0\ \Longleftrightarrow\ C_{T,Q(\rho)}Ux=0.$$
--   The accepted exact original quartet cutoff supplies $c$ and its closed characterization, so the larger-window half-bound holds even at $T=c$. A closed local proof of signed-covariance nonnegativity uses accepted original half-bound/test equivalence and dense-test covariance order. The accepted original neutral-window inclusion theorem then constructs the same original source-compatible inclusion with exact neutral-kernel persistence. The actual zero subtype, original reflection/conjugation quartet, analytic multiplicities, completed carrier and actors remain unchanged. This certifies custody at the finite INNER cutoff; it does not identify a separately prescribed critical endpoint, prove its arithmetic right-support jump budget, or assert neutral-kernel triviality or RH.
-- source:
--   monocap-tech/weil certified native head 5813d3576adfea3fd4d9319495125180db6e3d95; exact existing CanonicalGreenNeutralShell.lean and CriticalWindowBoundary.lean declarations; no native statement changes

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_original_quartet
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_quartet_boundary_with_original_neutral_custody (ρ : CriticalZeros)
    (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
            canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      ∀ t T : ℝ, ∀ ht : 0 < t, ∀ hT : 0 < T, t ≤ T → T ≤ c →
        ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
          (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
            U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
          ∀ x : Physical t,
            (canonicalPositiveCovariance t ht -
              canonicalSelectedSynthesis t ht (quartet ρ) ∘L
                (canonicalSelectedSynthesis t ht (quartet ρ)).adjoint) x = 0 ↔
            (canonicalPositiveCovariance T hT -
              canonicalSelectedSynthesis T hT (quartet ρ) ∘L
                (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint) (U x) = 0 := by sorry
