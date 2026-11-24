-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_zetaMul_eq_sum
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.zetaMul_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:08.125049+00:00
-- url     : https://prove2.me/theorems/f8523e16-b35c-477f-9c50-28f732c0613c
-- title:
--   Supply AP: zeta Mul eq sum
-- statement:
--   The Supply AP construction uses the zeta Mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L42-L48

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
set_option backward.isDefEq.respectTransparency.types false

theorem Formalism.HermitianLattices.Ext.SupplyAP.zetaMul_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    DirichletCharacter.zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by sorry
