-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero
-- name    : Formalism.FourierDecayAlt.P.B2x2.map_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:32.216807+00:00
-- url     : https://prove2.me/theorems/6aff5e12-c091-4a1a-a098-a30c547d0ab6
-- title:
--   B2x2: map ne zero
-- statement:
--   The B2x2 construction uses the map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L378-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L378-L384

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2

theorem Formalism.FourierDecayAlt.P.B2x2.map_ne_zero {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (h : μ ≠ 0) : μ.map f ≠ 0 := by sorry
