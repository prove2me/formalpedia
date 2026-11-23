-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_toSig_fst
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:56.068208+00:00
-- url     : https://prove2.me/theorems/0642d798-d8fa-42f2-a04b-8594b7b4143c
-- title:
--   Primitive Character Casts: to Sig fst
-- statement:
--   The Primitive Character Casts construction uses the to Sig fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean#L21-L22

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

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_fst {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : (toSig χ).1 + 1 = n := by sorry
