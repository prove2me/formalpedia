-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_le_dualF_of_gram
-- name    : Formalism.L2.SG.Pf.GluingBases.le_dualF_of_gram
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:16.017574+00:00
-- url     : https://prove2.me/theorems/5c7bf458-c9bf-4913-a93f-c4281264f46a
-- title:
--   Gluing Bases: le dual F of gram
-- statement:
--   The Gluing Bases construction uses the le dual F of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LeDualFOfGram.lean#L39-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LeDualFOfGram.lean#L39-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LeDualFOfGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.GluingBases.le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by sorry
