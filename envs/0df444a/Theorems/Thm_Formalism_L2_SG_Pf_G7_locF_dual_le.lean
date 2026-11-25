-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G7_locF_dual_le
-- name    : Formalism.L2.SG.Pf.G7.locF_dual_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:30.884885+00:00
-- url     : https://prove2.me/theorems/e21c2d23-d229-5b3d-8c45-db888f92bb4b
-- title:
--   G7: loc F dual le
-- statement:
--   The G7 construction uses the loc F dual le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFSubspace.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFSubspace.lean#L61-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G7
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G7.locF_dual_le (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) ≤ dualF h 𝔭 (locF 𝔭 L) := by sorry
