-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_isLattice_sup
-- name    : Formalism.L2.SG.Pf.G8.isLattice_sup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:51.95372+00:00
-- url     : https://prove2.me/theorems/1fcb3e38-98a1-561a-9137-706716572243
-- title:
--   G8: is Lattice sup
-- statement:
--   The G8 construction uses the is Lattice sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsLocFEq.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsLocFEq.lean#L30-L35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsLocFEq
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G8.isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) := by sorry
