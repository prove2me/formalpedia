-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:21.489118+00:00
-- url     : https://prove2.me/theorems/c218945a-d5f0-4020-b841-ec76c21c7b26
-- title:
--   Box Tail: tail mertens
-- statement:
--   The Box Tail construction uses the tail mertens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L61-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L61-L100

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailMertens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_mertens : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by sorry
