-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_mulVec
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.gram_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:06.54298+00:00
-- url     : https://prove2.me/theorems/6fad2c06-ad34-4755-9f3b-162e7f1c5b74
-- title:
--   Loc F: gram mul Vec
-- statement:
--   The Loc F construction uses the gram mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L161-L163

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem Formalism.HermitianLattices.Ext.L3.LocF.gram_mulVec (x : Fin n → V) (c : Fin n → K) (i : Fin n) :
    ((Matrix.of fun i j => h (x i) (x j)) *ᵥ c) i = h (x i) (∑ j, c j • x j) := by sorry
