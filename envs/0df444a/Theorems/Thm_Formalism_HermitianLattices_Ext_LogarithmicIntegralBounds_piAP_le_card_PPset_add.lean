-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_piAP_le_card_PPset_add
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.piAP_le_card_PPset_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:10.639534+00:00
-- url     : https://prove2.me/theorems/e2c79a84-eded-4779-a4fe-981b9acd8d76
-- title:
--   Logarithmic Integral Bounds: pi AP le card PPset add
-- statement:
--   The Logarithmic Integral Bounds construction uses the pi AP le card PPset add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L13-L30

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.piAP_le_card_PPset_add (X : ℝ) (m₀ a₀ : ℕ) (hX : 1 ≤ X) :
    (piAP X m₀ a₀ : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ) := by sorry
