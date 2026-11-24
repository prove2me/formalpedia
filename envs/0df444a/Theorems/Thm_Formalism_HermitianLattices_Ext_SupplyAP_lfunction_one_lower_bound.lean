-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_lfunction_one_lower_bound
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.lfunction_one_lower_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:44.262175+00:00
-- url     : https://prove2.me/theorems/7517957e-eece-4c82-82a5-d6672b9d6e68
-- title:
--   Supply AP: lfunction one lower bound
-- statement:
--   The Supply AP construction uses the lfunction one lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/LfunctionOneLowerBound.lean#L34-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/LfunctionOneLowerBound.lean#L34-L99

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.lfunction_one_lower_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    1 / (20 * ((q : ℝ) + 1)) ≤ (DirichletCharacter.LFunction χ 1).re := by sorry
