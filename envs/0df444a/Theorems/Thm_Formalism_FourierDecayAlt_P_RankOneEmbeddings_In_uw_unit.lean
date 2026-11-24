-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_uw_unit
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.uw_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:21:03.318288+00:00
-- url     : https://prove2.me/theorems/e6a8416d-ea19-46f6-96b9-3eccdd4e0bf2
-- title:
--   In: uw unit
-- statement:
--   The In construction uses the uw unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L857-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L857-L869

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.uw_unit {z : Vc k r} {h : Mat k r} (hh : h ∈ UWset k r z) : IsUnit h.det := by sorry
