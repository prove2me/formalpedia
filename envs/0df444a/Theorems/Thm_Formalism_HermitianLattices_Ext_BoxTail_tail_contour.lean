-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_contour
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_contour
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:53.711911+00:00
-- url     : https://prove2.me/theorems/6a854fc5-7a66-463e-8655-26e0fd0be0de
-- title:
--   Box Tail: tail contour
-- statement:
--   The Box Tail construction uses the tail contour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean#L14-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean#L14-L135

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailBox
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContour
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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_contour (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 800) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q z η : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ → 1 ≤ z → 0 < η → η ≤ 1 →
      ‖Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ ≤
        K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + δ) + z ^ 2 / Q) := by sorry
