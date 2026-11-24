-- Prove2me | Theorems.Thm_Formalism_H_gauss_fun_eq
-- name    : Formalism.H.gauss_fun_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:11.314809+00:00
-- url     : https://prove2.me/theorems/a32f3419-8856-49de-ab64-5c87c5b58d78
-- title:
--   H: gauss fun eq
-- statement:
--   The H construction uses the gauss fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L13-L20

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

theorem Formalism.H.gauss_fun_eq (t : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =
      fun v : V => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by sorry
