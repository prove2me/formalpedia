-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_left_pt
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_left_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:55.718689+00:00
-- url     : https://prove2.me/theorems/2d82edb8-fde4-437b-b1ca-ca673f561052
-- title:
--   Box Tail: tc left pt
-- statement:
--   The Box Tail construction uses the tc left pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L10-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L10-L68

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_left_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z η σ M : ℝ) (hz : 0 < z)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) (u : ℝ)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I) - Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) := by sorry
