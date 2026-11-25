-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G6_mem_ker_toDisc
-- name    : Formalism.L2.SG.Pf.G6.mem_ker_toDisc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:15.519868+00:00
-- url     : https://prove2.me/theorems/3da1ac07-06b1-50ee-ba10-2960b70b0c3a
-- title:
--   G6: mem ker to Disc
-- statement:
--   The G6 construction uses the mem ker to Disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscIsoOfProj.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscIsoOfProj.lean#L39-L45

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

theorem Formalism.L2.SG.Pf.G6.mem_ker_toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (x : ↥Λ) : x ∈ LinearMap.ker (toDisc h hc L Λ 𝔭 hP) ↔ prO hc (x : V) ∈ locF 𝔭 L := by sorry
