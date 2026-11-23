-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_map_scal_eq_comap
-- name    : Formalism.FourierDecayAlt.P.S6x5.map_scal_eq_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:30.705508+00:00
-- url     : https://prove2.me/theorems/c517f0d5-991f-451e-8305-7592846dc99c
-- title:
--   S6x5: map scal eq comap
-- statement:
--   The S6x5 construction uses the map scal eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L55-L67

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.FourierDecayAlt.P.S6x5.map_scal_eq_comap (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ V) :
    L.map (scal V c) = ZLattice.comap ℝ L (scalInv V c hc).toLinearMap := by sorry
