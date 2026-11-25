-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDecomposition_bigCell_one_fixes_vector
-- name    : Formalism.FourierDecayAlt.P.BigCellDecomposition.bigCell_one_fixes_vector
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:37.438743+00:00
-- url     : https://prove2.me/theorems/c1860e0f-6298-4eb9-a260-3b68fa6ded63
-- title:
--   Big Cell Decomposition: big Cell one fixes vector
-- statement:
--   The Big Cell Decomposition construction uses the big Cell one fixes vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDecomposition.lean#L25-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDecomposition.lean#L25-L56

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

theorem Formalism.FourierDecayAlt.P.BigCellDecomposition.bigCell_one_fixes_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by sorry
