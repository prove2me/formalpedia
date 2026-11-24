-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_FF_inv
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.FF_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:05.592035+00:00
-- url     : https://prove2.me/theorems/33e0b95e-9ead-47c6-a4c5-63a55d9792e7
-- title:
--   R1: FF inv
-- statement:
--   The R1 construction uses the FF inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L491-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L491-L503

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.FF_inv {z' : Vc k r} {μW' : Measure (Mt k r)} (hW' : IsHaarOn (UWset k r z') μW')
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (m : Mat k r) (h : Mat k r) (hh : h ∈ UWset k r z') :
    ∫⁻ h', f (mulM ((m * h : Mat k r), h')) ∂μW' = ∫⁻ h', f (mulM (m, h')) ∂μW' := by sorry
