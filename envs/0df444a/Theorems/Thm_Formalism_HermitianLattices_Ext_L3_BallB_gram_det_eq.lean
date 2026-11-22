-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_gram_det_eq
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.gram_det_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:21.172085+00:00
-- url     : https://prove2.me/theorems/ee76d63d-957d-4171-beb7-3531870effcc
-- title:
--   Ball B: gram det eq
-- statement:
--   The Ball B construction uses the gram det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapConjO.lean#L15-L29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]

theorem Formalism.HermitianLattices.Ext.L3.BallB.gram_det_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V) (u w : ι → V) :
    (Matrix.of fun i j => h (u i) (w j)).det =
      star (b.det u) * (Matrix.of fun i j => h (b i) (b j)).det * b.det w := by sorry
