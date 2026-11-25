-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_extension_identity_of_mem_compl
-- name    : Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.extension_identity_of_mem_compl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:27.360777+00:00
-- url     : https://prove2.me/theorems/7b9bd3d7-e455-5b28-9dd7-931ff2f95ff3
-- title:
--   Orthogonal Complement Genus Mass: extension identity of mem compl
-- statement:
--   The Orthogonal Complement Genus Mass construction uses the extension identity of mem compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L170-L174

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

theorem Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.extension_identity_of_mem_compl (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U))
    (w : ↥(orthK h U)) : extId hc g w = g w := by sorry
