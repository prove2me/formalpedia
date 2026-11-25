-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G6_prO_mem_iff
-- name    : Formalism.L2.SG.Pf.G6.prO_mem_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:22.488664+00:00
-- url     : https://prove2.me/theorems/8673161c-d021-5963-8b67-635ad57700ff
-- title:
--   G6: pr O mem iff
-- statement:
--   The G6 construction uses the pr O mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscIsoOfProj.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscIsoOfProj.lean#L47-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscIsoOfProj
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G6
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G6.prO_mem_iff {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by sorry
