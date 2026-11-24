-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_tail_small
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.tail_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:17.50339+00:00
-- url     : https://prove2.me/theorems/04aefb70-91ab-4784-a87d-9e3c1c23e0e3
-- title:
--   Supply AP: tail small
-- statement:
--   The Supply AP construction uses the tail small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/LfunctionOneLowerBound.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/LfunctionOneLowerBound.lean#L11-L32

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_LfunctionOneLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.tail_small {x : ℝ} (hx : 1 ≤ x) : x ^ 3 * (x + 1) * Real.exp (-(x ^ 3) / x) ≤ 48 / x ^ 4 := by sorry
