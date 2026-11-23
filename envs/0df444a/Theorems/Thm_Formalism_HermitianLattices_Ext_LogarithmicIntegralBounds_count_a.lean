-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_count_a
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:39.062748+00:00
-- url     : https://prove2.me/theorems/0828b62e-36c8-408e-aa54-100454e3c60b
-- title:
--   Logarithmic Integral Bounds: count a
-- statement:
--   The Logarithmic Integral Bounds construction uses the count a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L346-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L346-L397

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_a (hP : PNTAPRelW) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by sorry
