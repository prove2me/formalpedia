-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_jac_cls_eq_zero
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_jac_cls_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:34.544373+00:00
-- url     : https://prove2.me/theorems/0cb4fe17-49b2-444d-9d64-4971a0c5fe2c
-- title:
--   Logarithmic Integral Bounds: sum jac cls eq zero
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum jac cls eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L106-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L106-L114

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_jac_cls_eq_zero (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by sorry
