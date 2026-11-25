-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G7_dualF_locF_le
-- name    : Formalism.L2.SG.Pf.G7.dualF_locF_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:17.117297+00:00
-- url     : https://prove2.me/theorems/274e5e0c-a31a-546f-8729-0facf5202e51
-- title:
--   G7: dual F loc F le
-- statement:
--   The G7 construction uses the dual F loc F le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFSubspace.lean#L72-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFSubspace.lean#L72-L103

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

theorem Formalism.L2.SG.Pf.G7.dualF_locF_le (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : dualF h 𝔭 (locF 𝔭 L) ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) := by sorry
