-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_abelG
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.abelG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:54.278739+00:00
-- url     : https://prove2.me/theorems/2aa5bbcd-2ac3-4f89-adc7-575834808068
-- title:
--   Supply AP: abel G
-- statement:
--   The Supply AP construction uses the abel G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L83-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffAbel.lean#L83-L134

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset

theorem Formalism.HermitianLattices.Ext.SupplyAP.abelG (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)‖ ≤ ((q : ℝ) + 1) / 2 := by sorry
