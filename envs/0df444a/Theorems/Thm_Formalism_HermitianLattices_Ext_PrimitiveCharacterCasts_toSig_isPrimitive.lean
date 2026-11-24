-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_toSig_isPrimitive
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_isPrimitive
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:51.441581+00:00
-- url     : https://prove2.me/theorems/9397af3f-33b2-4bcc-bf1a-412f061d369c
-- title:
--   Primitive Character Casts: to Sig is Primitive
-- statement:
--   The Primitive Character Casts construction uses the to Sig is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L24-L26

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

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_isPrimitive {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (toSig χ).2.IsPrimitive ↔ χ.IsPrimitive := by sorry
