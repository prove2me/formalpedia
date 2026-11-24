-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_toSig_level_eq
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_level_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:37.189124+00:00
-- url     : https://prove2.me/theorems/300c2c5e-1aa9-4a14-9e9f-f97886cf5371
-- title:
--   Primitive Character Casts: to Sig level eq
-- statement:
--   The Primitive Character Casts construction uses the to Sig level eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L32-L37

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_level_eq {n m : ℕ} [NeZero n] [NeZero m] (χ : DirichletCharacter ℂ n) (ψ : DirichletCharacter ℂ m)
    (h : toSig χ = toSig ψ) : n = m := by sorry
