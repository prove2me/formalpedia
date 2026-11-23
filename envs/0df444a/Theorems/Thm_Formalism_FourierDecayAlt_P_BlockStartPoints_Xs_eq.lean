-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_Xs_eq
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.Xs_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:05.087519+00:00
-- url     : https://prove2.me/theorems/620f410b-4fc4-43a8-8825-c01af623e9b6
-- title:
--   Block Start Points: Xs eq
-- statement:
--   The Block Start Points construction uses the Xs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L73-L93

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

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.Xs_eq (T : Tower E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    Xs T i s = pts (T.X (i - s)) s (T.Sg (i - s + 1) s) := by sorry
