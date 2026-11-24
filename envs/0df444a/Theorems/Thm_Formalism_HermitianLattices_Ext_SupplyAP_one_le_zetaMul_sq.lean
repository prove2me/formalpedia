-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_one_le_zetaMul_sq
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:07.034531+00:00
-- url     : https://prove2.me/theorems/bf31771d-747a-443b-bc6d-7accaea83a6f
-- title:
--   Supply AP: one le zeta Mul sq
-- statement:
--   The Supply AP construction uses the one le zeta Mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L30-L39

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (k : ℕ)
    (hk : k ≠ 0) : 1 ≤ DirichletCharacter.zetaMul χ (k ^ 2) := by sorry
