-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excTerm_ofReal
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.excTerm_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:40.346383+00:00
-- url     : https://prove2.me/theorems/913a2fb3-d4df-4161-a308-70af8d8eb58b
-- title:
--   Supply AP: exc Term of Real
-- statement:
--   The Supply AP construction uses the exc Term of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcTerm.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcTerm.lean#L37-L39

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
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

theorem Formalism.HermitianLattices.Ext.SupplyAP.excTerm_ofReal (x β : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ (β : ℂ) / (β : ℂ) = ((x ^ β / β : ℝ) : ℂ) := by sorry
