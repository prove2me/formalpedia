-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens_psi
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_mertens_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:44.498217+00:00
-- url     : https://prove2.me/theorems/deb51dd7-a565-460e-8f7b-020c6d1f321b
-- title:
--   Box Tail: tail mertens psi
-- statement:
--   The Box Tail construction uses the tail mertens psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailMertens.lean#L9-L24

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_mertens_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by sorry
