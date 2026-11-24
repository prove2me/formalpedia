-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_mainAP_lower
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mainAP_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:36.528736+00:00
-- url     : https://prove2.me/theorems/335e389d-53b4-4005-a4a9-a8eb05b07128
-- title:
--   Logarithmic Integral Bounds: main AP lower
-- statement:
--   The Logarithmic Integral Bounds construction uses the main AP lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L86-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L86-L173

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mainAP_lower {M : ℕ} [NeZero M] (h8 : 8 ∣ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (M : ℝ) ^ (-1 : ℝ))
    (b : ℕ) (X : ℝ) (hX : 0 < X) (hY : 4 ≤ Real.log X) :
    c * X / (2 * Real.log X * (M : ℝ) ^ 2) ≤ mainAP e b X := by sorry
