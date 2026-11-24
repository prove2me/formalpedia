-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_exists_G
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.exists_G
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:08.422258+00:00
-- url     : https://prove2.me/theorems/d9322ec9-f711-4d89-b23b-08346428c91b
-- title:
--   R1: exists G
-- statement:
--   The R1 construction uses the exists G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L432-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L432-L469

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.exists_G (CWb : ClosedWb) (z' : Vc k r) (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ m : Mat k r, ∀ h ∈ UWset k r z', F (m * h : Mat k r) = F m) :
    ∃ G : Vc k r → ℝ≥0∞, Measurable G ∧ ∀ m ∈ UWb k r, F m = G (m *ᵥ z') := by sorry
