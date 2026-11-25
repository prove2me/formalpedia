-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_mem_push
-- name    : Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.mem_push
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:45.721391+00:00
-- url     : https://prove2.me/theorems/8bf38018-ad8d-4edb-bf21-6de0975a9f22
-- title:
--   Orthogonal Complement Genus Mass: mem push
-- statement:
--   The Orthogonal Complement Genus Mass construction uses the mem push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L34-L35

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

theorem Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {v : V} :
    v ∈ push X L ↔ ∃ x ∈ L, (x : V) = v := by sorry
