-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_genus_of_fib
-- name    : Formalism.L2.SG.Pf.G8.genus_of_fib
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:02.039601+00:00
-- url     : https://prove2.me/theorems/342f66d8-5ef4-556e-ba63-af3929ac6e2d
-- title:
--   G8: genus of fib
-- statement:
--   The G8 construction uses the genus of fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L102-L129

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

theorem Formalism.L2.SG.Pf.G8.genus_of_fib (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    {T : Submodule (𝓞 K) V} (hT : IsLatIn (orthK h U) T)
    (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T := by sorry
