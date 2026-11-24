-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_geomIcc
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.geomIcc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:01.279219+00:00
-- url     : https://prove2.me/theorems/9a1ac693-c361-4df6-bc89-fcecd65a298f
-- title:
--   Supply AP: geom Icc
-- statement:
--   The Supply AP construction uses the geom Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L50-L58

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.geomIcc (u : ℝ) (hu : u ≠ 1) (M : ℕ) :
    ∑ m ∈ Icc 1 M, u ^ m = (u - u ^ (M + 1)) / (1 - u) := by sorry
