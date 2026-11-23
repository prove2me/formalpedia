-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_diff_schi
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:13.411463+00:00
-- url     : https://prove2.me/theorems/e0b426cb-891c-4310-8a30-34784169145a
-- title:
--   Box Tail: tail diff schi
-- statement:
--   The Box Tail construction uses the tail diff schi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailDiff.lean#L67-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailDiff.lean#L67-L86

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailDiff
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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hz : 1 ≤ z) (hh : 0 < h) :
    ‖Formalism.ZeroFreeDirichlet.Schi χ (z + h) - Formalism.ZeroFreeDirichlet.Schi χ z -
              (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)‖ ≤
      h * (h + 1) * Real.log (z + h) / z := by sorry
