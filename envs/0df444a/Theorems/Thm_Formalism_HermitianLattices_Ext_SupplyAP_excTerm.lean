-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excTerm
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.excTerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:54.500797+00:00
-- url     : https://prove2.me/theorems/062e73e1-be58-4a13-8098-446738558ccf
-- title:
--   Supply AP: exc Term
-- statement:
--   The Supply AP construction uses the exc Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcTerm.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcTerm.lean#L7-L35

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.excTerm (x β : ℝ) (hx : 0 < x) (hL : 4 ≤ Real.log x) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1) :
    x ^ β / β ≤ x * (1 - (1 - β) / 2) := by sorry
