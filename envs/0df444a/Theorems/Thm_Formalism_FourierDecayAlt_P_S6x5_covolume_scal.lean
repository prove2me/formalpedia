-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_covolume_scal
-- name    : Formalism.FourierDecayAlt.P.S6x5.covolume_scal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:31.530109+00:00
-- url     : https://prove2.me/theorems/111b9883-9240-49f1-86fa-7e70e0e3cea3
-- title:
--   S6x5: covolume scal
-- statement:
--   The S6x5 construction uses the covolume scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L69-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L69-L92

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

theorem Formalism.FourierDecayAlt.P.S6x5.covolume_scal (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) (hc : c ≠ 0) :
    ZLattice.covolume (ZLattice.comap ℝ L (scalInv V c hc).toLinearMap) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume L μ := by sorry
