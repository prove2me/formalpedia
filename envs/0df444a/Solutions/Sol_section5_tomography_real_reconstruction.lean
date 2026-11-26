-- Prove2me | solution 1 for section5_tomography_real_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:54.035905+00:00
-- url     : https://prove2.me/submissions/6943f0a5-4f3e-462f-9339-5cfaccf01164

import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_section5_real_direction_recovery
import Theorems.Thm_section5_spectral_estimator_exists
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Statistical operator error implies the real, sign-ambiguous direction guarantee
used by Theorem 5.6. This is the reconstruction guarantee; no efficient measurement
or classical eigenvector algorithm is assumed to have been constructed here. -/

theorem section5_complexify_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖section5_complexify w‖=‖w‖ := by
  have hs : ‖section5_complexify w‖^2=‖w‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,section5_complexify,WithLp.ofLp_toLp,
      Complex.norm_real]
  nlinarith [norm_nonneg w,norm_nonneg (section5_complexify w)]



end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖=1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖L-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/96 →
        let r := if ‖section5_imag_part v‖ ≤ ‖section5_real_part v‖ then
          section5_real_part v else section5_imag_part v
        r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨v,hv,hrecover⟩ := section5_spectral_estimator_exists L hL
  refine ⟨v,hv,?_⟩
  intro w hw ε hε hε' herror
  obtain ⟨ζ,hζ,hclose⟩ := hrecover (section5_complexify w)
    (by rwa [section5_complexify_norm]) (ε/96) (by positivity) (by linarith) herror
  have hh := section5_real_direction_recovery v w ζ ε hv hw hε hε' (by linarith)
  exact hh
