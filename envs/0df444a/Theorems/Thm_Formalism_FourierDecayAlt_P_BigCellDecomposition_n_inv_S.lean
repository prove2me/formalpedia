-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDecomposition_n_inv_S
-- name    : Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:46.622798+00:00
-- url     : https://prove2.me/theorems/eb3a4382-e1e0-4c66-a7e6-05c3b48aba4d
-- title:
--   Big Cell Decomposition: n inv S
-- statement:
--   The Big Cell Decomposition construction uses the n inv S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDecomposition.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDecomposition.lean#L58-L59

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDecomposition
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z := by sorry
