-- Prove2me | Theorems.Thm_Formalism_H_gauss_decay
-- name    : Formalism.H.gauss_decay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:24.507804+00:00
-- url     : https://prove2.me/theorems/40eb078d-90c5-4602-b9ba-ded8a7d92270
-- title:
--   H: gauss decay
-- statement:
--   The H construction uses the gauss decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/GaussSchwartz.lean#L27-L38

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

theorem Formalism.H.gauss_decay (t : ℝ) (ht : 0 < t) (b : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =O[cocompact V]
      (fun v => ‖v‖ ^ (-b)) := by sorry
