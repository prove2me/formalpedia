-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_cnt_add_small
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.cnt_add_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:49.605534+00:00
-- url     : https://prove2.me/theorems/8045df49-df13-4ff0-bb92-6973d987386b
-- title:
--   Logarithmic Integral Bounds: cnt add small
-- statement:
--   The Logarithmic Integral Bounds construction uses the cnt add small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L67-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L67-L96

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.cnt_add_small (m₀ s a₀ : ℕ) (X : ℝ) (b : ℕ) (hb : b ∈ clsB m₀ s a₀) :
    ((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card + smallCnt X (m₀ * s) b = piAP X (m₀ * s) b := by sorry
