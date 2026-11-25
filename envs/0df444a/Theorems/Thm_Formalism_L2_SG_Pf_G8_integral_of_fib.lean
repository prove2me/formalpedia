-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_integral_of_fib
-- name    : Formalism.L2.SG.Pf.G8.integral_of_fib
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:29:56.652583+00:00
-- url     : https://prove2.me/theorems/2b93187d-c29d-4946-b45a-eda139783e88
-- title:
--   G8: integral of fib
-- statement:
--   The G8 construction uses the integral of fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L83-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L83-L100

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibPNeZeroOfGenus
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPermOfMin
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

theorem Formalism.L2.SG.Pf.G8.integral_of_fib (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h T := by sorry
