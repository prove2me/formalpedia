-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_coprime_of_cls
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.coprime_of_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:47.600793+00:00
-- url     : https://prove2.me/theorems/f8a34afa-4196-4c76-9548-da23f479a9b1
-- title:
--   Logarithmic Integral Bounds: coprime of cls
-- statement:
--   The Logarithmic Integral Bounds construction uses the coprime of cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L12-L17

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.coprime_of_cls {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) : b.Coprime (m₀ * s) := by sorry
