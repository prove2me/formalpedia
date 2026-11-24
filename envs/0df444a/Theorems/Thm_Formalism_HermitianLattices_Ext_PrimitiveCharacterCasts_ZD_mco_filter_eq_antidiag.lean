-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_filter_eq_antidiag
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_filter_eq_antidiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:07.375644+00:00
-- url     : https://prove2.me/theorems/c3bfcd56-4652-44f1-9ae1-568ea3f1792d
-- title:
--   ZD: mco filter eq antidiag
-- statement:
--   The ZD construction uses the mco filter eq antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean#L23-L39

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

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_filter_eq_antidiag {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by sorry
