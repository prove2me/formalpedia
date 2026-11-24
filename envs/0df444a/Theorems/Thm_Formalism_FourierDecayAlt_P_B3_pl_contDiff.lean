-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_contDiff
-- name    : Formalism.FourierDecayAlt.P.B3.pl_contDiff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:16.126342+00:00
-- url     : https://prove2.me/theorems/eb018187-c907-4d33-a4a3-1f5cd00a040b
-- title:
--   B3: pl cont Diff
-- statement:
--   The B3 construction uses the pl cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L23-L26

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.B3.pl_contDiff (a b k : ℝ) : ContDiff ℝ 2 (pl a b k) := by sorry
