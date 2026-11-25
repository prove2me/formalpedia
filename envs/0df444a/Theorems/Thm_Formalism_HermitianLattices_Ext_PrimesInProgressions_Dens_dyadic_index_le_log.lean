-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_index_le_log
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_index_le_log
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:33.569149+00:00
-- url     : https://prove2.me/theorems/dd9bf8db-66e9-4c41-a18f-7b76559f7979
-- title:
--   Dens: dyadic index le log
-- statement:
--   The Dens construction uses the dyadic index le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/OneLeLogOfThreeLe.lean#L39-L51

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_index_le_log (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by sorry
