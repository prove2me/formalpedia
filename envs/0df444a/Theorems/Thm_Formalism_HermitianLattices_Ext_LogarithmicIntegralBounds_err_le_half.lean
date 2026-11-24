-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_err_le_half
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.err_le_half
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:28.10743+00:00
-- url     : https://prove2.me/theorems/7a28c436-1af3-4b06-98ec-4a0d773888cf
-- title:
--   Logarithmic Integral Bounds: err le half
-- statement:
--   The Logarithmic Integral Bounds construction uses the err le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L205-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L205-L237

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.err_le_half {A c₃ Y Λ l : ℝ} (hc₃ : 0 < c₃) (hΛ : 0 < Λ) (hYΛ : l ^ 2 / 4 * Λ ≤ Y)
    (hYl : l ^ 2 / 4 ≤ Y)
    (hK1 : Real.log (4 * (|A| + 1)) ≤ c₃ * (l ^ 2 / 4))
    (hK2 : Real.log (4 * (|A| + 1)) ^ 2 ≤ c₃ * (l ^ 2 / 4)) :
    |A| * (Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y))) ≤ 1 / 2 := by sorry
