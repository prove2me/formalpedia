-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_one_le_zetaMul_prime_pow_even
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_prime_pow_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:07.865801+00:00
-- url     : https://prove2.me/theorems/b9b33635-f1eb-4673-b468-4c62b741a32a
-- title:
--   Supply AP: one le zeta Mul prime pow even
-- statement:
--   The Supply AP construction uses the one le zeta Mul prime pow even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L11-L28

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_prime_pow_even {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (a : ℕ) : 1 ≤ DirichletCharacter.zetaMul χ (p ^ (2 * a)) := by sorry
