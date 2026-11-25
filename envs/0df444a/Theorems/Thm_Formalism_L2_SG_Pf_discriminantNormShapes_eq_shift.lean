-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_eq_shift
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.eq_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:49:40.126618+00:00
-- url     : https://prove2.me/theorems/1b31d4e2-7e51-440f-8697-1f651cb35c26
-- title:
--   discriminant Norm Shapes: eq shift
-- statement:
--   The discriminant Norm Shapes construction uses the eq shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagQConjTranspose.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagQConjTranspose.lean#L67-L74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem Formalism.L2.SG.Pf.discriminantNormShapes.eq_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    (P W Z Z' : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    W + Pᴴ * (Z + Z') + (Z + Z')ᴴ * P + (Z + Z')ᴴ * diagQ K 𝔭 k a * (Z + Z') =
      (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) + (P + diagQ K 𝔭 k a * Z)ᴴ * Z' +
        Z'ᴴ * (P + diagQ K 𝔭 k a * Z) + Z'ᴴ * diagQ K 𝔭 k a * Z' := by sorry
