-- Prove2me | solution 1 for section5_tomography_spectral_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:48.005988+00:00
-- url     : https://prove2.me/submissions/1be7e250-7aa2-4f41-84d4-2cc02b15475c

import Mathlib
import Theorems.Thm_section5_tomography_eigenvector_recovery
import Theorems.Thm_section5_tomography_rayleigh_lower
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v)
    (hmax : ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam) :
    ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by
  have hlam := section5_tomography_rayleigh_lower L w hw η lam herror hmax
  exact section5_tomography_eigenvector_recovery L w v hw hv η lam hη hη' (by linarith)
    herror heigen
