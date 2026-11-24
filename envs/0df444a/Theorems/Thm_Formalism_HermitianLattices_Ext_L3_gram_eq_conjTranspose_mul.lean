-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gram_eq_conjTranspose_mul
-- name    : Formalism.HermitianLattices.Ext.L3.gram_eq_conjTranspose_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:02.398813+00:00
-- url     : https://prove2.me/theorems/2d963b9f-b4d4-42b7-9a58-e4edf4a63caf
-- title:
--   L3: gram eq conj Transpose mul
-- statement:
--   The L3 construction uses the gram eq conj Transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GramEqConjTransposeMul.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GramEqConjTransposeMul.lean#L10-L20

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GramEqConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3

theorem Formalism.HermitianLattices.Ext.L3.gram_eq_conjTranspose_mul {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    gram h b = (b'.toMatrix b).conjTranspose * gram h b' * b'.toMatrix b := by sorry
