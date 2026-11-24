-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_linearIndependent_of_gram_det_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.linearIndependent_of_gram_det_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:34.709019+00:00
-- url     : https://prove2.me/theorems/267c9273-d0c4-4c41-8886-94237781d173
-- title:
--   Loc F: linear Independent of gram det ne zero
-- statement:
--   The Loc F construction uses the linear Independent of gram det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L165-L172

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

theorem Formalism.HermitianLattices.Ext.L3.LocF.linearIndependent_of_gram_det_ne_zero (x : Fin n → V)
    (hdet : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0) : LinearIndependent K x := by sorry
