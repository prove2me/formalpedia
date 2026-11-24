-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_filter_subset_antidiag
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_filter_subset_antidiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:01.13801+00:00
-- url     : https://prove2.me/theorems/b72849e1-a50f-48e1-9239-82f95066c87a
-- title:
--   ZD: mco filter subset antidiag
-- statement:
--   The ZD construction uses the mco filter subset antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean#L41-L46

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_filter_subset_antidiag {Y N n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by sorry
