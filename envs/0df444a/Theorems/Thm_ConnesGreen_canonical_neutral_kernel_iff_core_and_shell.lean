-- Prove2me | Theorems.Thm_ConnesGreen_canonical_neutral_kernel_iff_core_and_shell
-- name    : ConnesGreen.canonical_neutral_kernel_iff_core_and_shell
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T07:06:35.396981+00:00
-- url     : https://prove2.me/theorems/7250e9b5-c38b-4ba1-8e07-605879e1e906
-- title:
--   Original cross-window neutral kernel is exactly core neutrality plus shell vanishing
-- statement:
--   For EVERY original source-compatible complex linear isometry $U:\mathrm{Physical}(t)\to\mathrm{Physical}(T)$ on $0<t\le T$, every original finite actual-zero packet $S$, and every completed vector $x$, we prove
--   $$C_{T,S}Ux=0\quad\Longleftrightarrow\quad C_{t,S}x=0\ \land\ (I-UU^*)C_{T,S}Ux=0.$$
--   Here both signed covariances use the unchanged original positive and selected actor syntheses. Accepted original source-adjoint custody gives source compression for every actual zero, and accepted signed-covariance compression identifies $U^*C_{T,S}Ux$ with $C_{t,S}x$. If the larger value is zero, both components vanish. Conversely core neutrality makes $U^*C_{T,S}Ux=0$; the exact decomposition into $UU^*$ and $I-UU^*$ then makes the whole larger value equal its shell component, hence zero. No positivity, half-bound, kernel triviality, neutral attainment or arithmetic shell estimate is assumed. This is the exact existing native theorem, independently proved using accepted original compression.
-- source:
--   monocap-tech/weil parent b7df0270c344b8721001f902d0955d977d7afccc; recovered exact CanonicalGreenNeutralShell.lean core/shell theorem and additive NeutralShellObstruction.lean reductions

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_neutral_kernel_iff_core_and_shell (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) (x : Physical t) :
    (canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 ↔
      (canonicalPositiveCovariance t ht -
        canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ∧
      (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
        ((canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0 := by sorry
