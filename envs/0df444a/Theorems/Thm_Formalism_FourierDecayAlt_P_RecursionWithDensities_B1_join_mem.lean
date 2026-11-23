-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_join_mem
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.join_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:59.601025+00:00
-- url     : https://prove2.me/theorems/44f62ebb-03f6-4fc9-805c-88b6ebae0d4d
-- title:
--   B1: join mem
-- statement:
--   The B1 construction uses the join mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L646-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L646-L679

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.join_mem (T : Tower E) {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {t : E}
    (ht : t ∈ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∈ T.X i ↔ h ∈ T.X (i - s) := by sorry
