-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_swap_meas
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.swap_meas
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:54.77683+00:00
-- url     : https://prove2.me/theorems/d7831a4b-fd7f-4b81-adab-99ac96719a80
-- title:
--   In: swap meas
-- statement:
--   The In construction uses the swap meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L881-L900
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L881-L900

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.swap_meas {z : Vc k r} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : IsHaarOn (UWset k r z) μW) (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) :
    (μW.prod μN).map m1 = (μW.prod μN).map mulM := by sorry
