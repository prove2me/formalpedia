-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens_nat
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_mertens_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:59.225566+00:00
-- url     : https://prove2.me/theorems/ee701226-e9e7-4428-a76d-2e1cb961c531
-- title:
--   Box Tail: tail mertens nat
-- statement:
--   The Box Tail construction uses the tail mertens nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L26-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L26-L59

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_mertens_nat (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by sorry
