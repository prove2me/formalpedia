-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_box_sum
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_box_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:02.618924+00:00
-- url     : https://prove2.me/theorems/3e2bfb0f-6380-4437-a9b4-84da74580d35
-- title:
--   Box Tail: tail box sum
-- statement:
--   The Box Tail construction uses the tail box sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L26-L33

import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_box_sum {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by sorry
