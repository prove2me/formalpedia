-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_nonneg
-- name    : Formalism.FourierDecayAlt.P.B3.pl_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:33.953088+00:00
-- url     : https://prove2.me/theorems/69ca9683-d4bf-4ec0-89d9-db78f0a28115
-- title:
--   B3: pl nonneg
-- statement:
--   The B3 construction uses the pl nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L14-L16

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

theorem Formalism.FourierDecayAlt.P.B3.pl_nonneg (a b k x : ℝ) : 0 ≤ pl a b k x := by sorry
