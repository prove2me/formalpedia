-- Prove2me | Theorems.Thm_Formalism_REAL_TrPow_m_succ
-- name    : Formalism.REAL.TrPow_m_succ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:56.875796+00:00
-- url     : https://prove2.me/theorems/c0f4d712-b8fe-425d-913e-e7bac415f034
-- title:
--   REAL: Tr Pow m succ
-- statement:
--   The REAL construction uses the Tr Pow m succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/TrPowSumFilterZero.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/TrPowSumFilterZero.lean#L15-L17

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.TrPow_m_succ {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b := by sorry
