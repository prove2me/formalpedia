-- Prove2me | Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
-- name    : ConnesGreen.covariance_le_iff_original_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:16:33.380334+00:00
-- url     : https://prove2.me/theorems/3421a254-f32b-4ead-b475-efd276206413
-- title:
--   Original admissible tests detect exact physical covariance order
-- statement:
--   For every positive original support window $t$, self-adjoint bounded operator $A$ on its original physical carrier, and bounded synthesis $N:K\to\operatorname{Physical}(t)$ from any complex Hilbert space $K$, $$NN^*\le A\quad\Longleftrightarrow\quad\forall g\text{ original admissible at }t,\ \|N^*\operatorname{sourceEmbed}_t(Lg)\|^2\le\operatorname{Re}\langle A\operatorname{sourceEmbed}_t(Lg),\operatorname{sourceEmbed}_t(Lg)\rangle.$$ The original admissible vectors are dense by the accepted original density theorem. Continuity extends the quadratic inequality to the completed carrier; the self-adjoint quadratic criterion is exact. No arithmetic inequality is postulated.
-- source:
--   monocap-tech/weil at 7c5b1bc48d1cd2dd7385b1e634cd33a1e95550c7. CanonicalGreenTestDensity.lean, CanonicalGreenQuadraticEndpoint.lean and CriticalWindowBoundary.lean. Exact native definitions are unfolded only where no separate platform definition exists; native Lean checks these public statements against the originals.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.covariance_le_iff_original_tests (t : ℝ) (ht : 0 < t)
    (A : Physical t →L[ℂ] Physical t) (hA : IsSelfAdjoint A)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : K →L[ℂ] Physical t) :
    N ∘L N.adjoint ≤ A ↔ ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖N.adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
        RCLike.re ⟪A (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ := by sorry
