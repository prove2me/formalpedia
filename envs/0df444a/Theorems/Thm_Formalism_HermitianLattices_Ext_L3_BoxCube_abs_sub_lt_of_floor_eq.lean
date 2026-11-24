-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_abs_sub_lt_of_floor_eq
-- name    : Formalism.HermitianLattices.Ext.L3.BoxCube.abs_sub_lt_of_floor_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:10.3288+00:00
-- url     : https://prove2.me/theorems/e9efd74d-f86c-4e98-b85d-4e4abbd45c6a
-- title:
--   Box Cube: abs sub lt of floor eq
-- statement:
--   The Box Cube construction uses the abs sub lt of floor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormLeOfMemIdeal.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormLeOfMemIdeal.lean#L54-L65

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxCube.abs_sub_lt_of_floor_eq {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by sorry
