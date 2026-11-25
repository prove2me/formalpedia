-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_form_orth_U
-- name    : Formalism.L2.SG.Pf.GluedFormOrthogonality.form_orth_U
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:27.883749+00:00
-- url     : https://prove2.me/theorems/ba460f3c-8bbb-58e0-b5ac-d5057c11df8b
-- title:
--   Glued Form Orthogonality: form orth U
-- statement:
--   The Glued Form Orthogonality construction uses the form orth U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L21-L23

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

theorem Formalism.L2.SG.Pf.GluedFormOrthogonality.form_orth_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V} {u z : V}
    (hu : u ∈ U) (hz : z ∈ orthK h U) : h z u = 0 := by sorry
