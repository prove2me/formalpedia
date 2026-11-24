-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_regroup
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.regroup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:59.301457+00:00
-- url     : https://prove2.me/theorems/4764d139-675f-43ad-890b-24270fea6019
-- title:
--   Supply AP: regroup
-- statement:
--   The Supply AP construction uses the regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L124-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L124-L158

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
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
open scoped ComplexOrder

theorem Formalism.HermitianLattices.Ext.SupplyAP.regroup (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d (d * m) := by sorry
