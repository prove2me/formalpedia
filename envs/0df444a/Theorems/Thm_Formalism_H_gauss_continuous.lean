-- Prove2me | Theorems.Thm_Formalism_H_gauss_continuous
-- name    : Formalism.H.gauss_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:04.679645+00:00
-- url     : https://prove2.me/theorems/880738c8-47da-42cd-b7ec-860c303203c2
-- title:
--   H: gauss continuous
-- statement:
--   The H construction uses the gauss continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L22-L25

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

theorem Formalism.H.gauss_continuous (t : ℝ) :
    Continuous (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) := by sorry
