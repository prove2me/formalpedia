-- Prove2me | Theorems.Thm_Formalism_H_gauss_fourier
-- name    : Formalism.H.gauss_fourier
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:37.171806+00:00
-- url     : https://prove2.me/theorems/d14888be-4f84-4c31-851c-9d717dd02eb1
-- title:
--   H: gauss fourier
-- statement:
--   The H construction uses the gauss fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L40-L58

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.H.gauss_fourier (t : ℝ) (ht : 0 < t) (w : V) :
    (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) w =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) := by sorry
