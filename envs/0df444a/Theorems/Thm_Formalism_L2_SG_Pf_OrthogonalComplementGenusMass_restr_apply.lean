-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_restr_apply
-- name    : Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.restr_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:33.197077+00:00
-- url     : https://prove2.me/theorems/ca79b845-69a0-4094-8851-c0e10eb1b071
-- title:
--   Orthogonal Complement Genus Mass: restr apply
-- statement:
--   The Orthogonal Complement Genus Mass construction uses the restr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L202-L204

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

theorem Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.restr_apply {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (w : ↥(orthK h U)) :
    (restr hg w : V) = g w := by sorry
