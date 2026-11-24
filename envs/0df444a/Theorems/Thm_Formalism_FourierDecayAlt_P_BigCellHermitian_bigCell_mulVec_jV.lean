-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_bigCell_mulVec_jV
-- name    : Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:44:31.129313+00:00
-- url     : https://prove2.me/theorems/e0458d05-8f0d-44e4-840b-b32ebf746053
-- title:
--   Big Cell Hermitian: big Cell mul Vec j V
-- statement:
--   The Big Cell Hermitian construction uses the big Cell mul Vec j V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellHermitian.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellHermitian.lean#L17-L35

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellHermitian
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by sorry
