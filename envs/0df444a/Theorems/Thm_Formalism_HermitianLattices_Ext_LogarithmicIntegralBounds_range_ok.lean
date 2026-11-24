-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_range_ok
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.range_ok
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:29.119292+00:00
-- url     : https://prove2.me/theorems/33364835-7827-4bd6-89cc-699eedac5dfd
-- title:
--   Logarithmic Integral Bounds: range ok
-- statement:
--   The Logarithmic Integral Bounds construction uses the range ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L239-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L239-L273

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.range_ok {C₀ ε x Λ Y : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) (hΛ : 1 ≤ Λ) (hl1 : 1 ≤ Real.log x)
    (hl : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Λ ≤ Y) (h3 : Y ≤ x ^ (ε / 5) * Real.log x ^ 2) :
    C₀ * Λ * Real.log (Λ + 2) ≤ Y := by sorry
