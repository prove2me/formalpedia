-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow
-- name    : Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:36.503891+00:00
-- url     : https://prove2.me/theorems/248ea2d3-b1c7-4b74-ab83-3d025a5d1622
-- title:
--   Mean B: comap ext P pow
-- statement:
--   The Mean B construction uses the comap ext P pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L152-L154

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (extP K 𝔭 ^ k).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 ^ k := by sorry
