-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_sum_blocks
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.sum_blocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:36.950493+00:00
-- url     : https://prove2.me/theorems/1fea7572-e6e0-4516-9313-e5baa2866cbc
-- title:
--   ZD: sum blocks
-- statement:
--   The ZD construction uses the sum blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean#L10-L18

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.sum_blocks (f : ℕ → ℂ) (Y : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Ioc Y (Y * 2 ^ J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (Y * 2 ^ j) (2 * (Y * 2 ^ j)), f n
  := by sorry
