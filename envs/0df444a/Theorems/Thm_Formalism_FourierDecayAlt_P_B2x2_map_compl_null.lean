-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_compl_null
-- name    : Formalism.FourierDecayAlt.P.B2x2.map_compl_null
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:54:55.853797+00:00
-- url     : https://prove2.me/theorems/be328634-8b71-4f5a-ab54-59aaac742d3f
-- title:
--   B2x2: map compl null
-- statement:
--   The B2x2 construction uses the map compl null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L371-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L371-L376

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

theorem Formalism.FourierDecayAlt.P.B2x2.map_compl_null {X : Type*} [MeasurableSpace X] {k r : ℕ} (V : Set (Mat k r)) (hV : IsClosed V) (μ : Measure X)
    (f : X → Mt k r) (hf : Measurable f) (h : μ {x | f x ∉ V} = 0) : (μ.map f) Vᶜ = 0 := by sorry
