-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_blockStart_join
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.blockStart_join
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:02.350806+00:00
-- url     : https://prove2.me/theorems/e39527dc-924a-4549-baf4-6e565edd744d
-- title:
--   Block Start Points: block Start join
-- statement:
--   The Block Start Points construction uses the block Start join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.blockStart_join (h : Pt E) (s : ℕ) (t : E) (k : ℕ) (hk : k ≤ h.length) :
    blockStart (join h s t) k = blockStart h k := by sorry
