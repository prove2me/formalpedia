-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_form_U_orth
-- name    : Formalism.L2.SG.Pf.GluedFormOrthogonality.form_U_orth
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:20.555647+00:00
-- url     : https://prove2.me/theorems/06e0684c-9bac-5cfd-ac20-45f49e62607b
-- title:
--   Glued Form Orthogonality: form U orth
-- statement:
--   The Glued Form Orthogonality construction uses the form U orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueInlInl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluedFormOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.GluedFormOrthogonality.form_U_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {u z : V} (hu : u ∈ U)
    (hz : z ∈ orthK h U) : h u z = 0 := by sorry
