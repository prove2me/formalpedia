-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_le_ph_sub
-- name    : Formalism.LatticeIndexTer.le_ph_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:29.840563+00:00
-- url     : https://prove2.me/theorems/08e54c58-7647-4ca3-97c1-1c3ad2d7f052
-- title:
--   Lattice Index Ter: le ph sub
-- statement:
--   The Lattice Index Ter construction uses the le ph sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SumInterlacedBoundFails.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SumInterlacedBoundFails.lean#L23-L32

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset

theorem Formalism.LatticeIndexTer.le_ph_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log a ≤ ph b - ph a := by sorry
