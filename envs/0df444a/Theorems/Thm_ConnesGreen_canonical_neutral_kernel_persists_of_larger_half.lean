-- Prove2me | Theorems.Thm_ConnesGreen_canonical_neutral_kernel_persists_of_larger_half
-- name    : ConnesGreen.canonical_neutral_kernel_persists_of_larger_half
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:46:38.924293+00:00
-- url     : https://prove2.me/theorems/90fff757-9666-41ab-9e2e-88bdacfd50a2
-- title:
--   Original neutral kernel persists under a larger-window inner half-bound
-- statement:
--   For original windows $0<t\le T$, an original finite actual-zero packet $S$ and EVERY original complex linear isometry $U:\operatorname{Physical}(t)\to\operatorname{Physical}(T)$ preserving source embeddings of ALL original supported tests at $t$, we prove
--   $$\tfrac12 I\le G_S(T)\quad\Longrightarrow\quad C_{t,S}x=0\ \Longleftrightarrow\ C_{T,S}Ux=0$$
--   for EVERY completed-carrier vector $x$, where $C_{T,S}=P_TP_T^*-M_{T,S}M_{T,S}^*$ uses the unchanged original actor synthesis. The accepted original source-adjoint custody theorem gives exact source compression for every actual zero. A closed local proof of half-bound-to-signed-covariance nonnegativity uses accepted original half-bound/test equivalence and original dense-test covariance order. The accepted original nonnegative source-compression kernel theorem then proves the equivalence. Larger-window positivity is discharged by its concrete inner half-bound; no neutral-shell vanishing or kernel triviality is assumed.
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

theorem ConnesGreen.canonical_neutral_kernel_persists_of_larger_half (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) (x : Physical t) :
    (canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
      (canonicalPositiveCovariance T hT -
        canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by sorry
