-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_herm_bigCell
-- name    : Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:44:07.270876+00:00
-- url     : https://prove2.me/theorems/9fff25de-59a4-43f7-a567-dfda547e3cb6
-- title:
--   Big Cell Hermitian: herm big Cell
-- statement:
--   The Big Cell Hermitian construction uses the herm big Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellHermitian.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellHermitian.lean#L37-L41

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

theorem Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by sorry
