-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_locF_subset_span
-- name    : Formalism.L2.SG.Pf.GluingBases.locF_subset_span
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:22.040802+00:00
-- url     : https://prove2.me/theorems/318911a6-87e8-503d-8bce-85553a52e747
-- title:
--   Gluing Bases: loc F subset span
-- statement:
--   The Gluing Bases construction uses the loc F subset span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LinearIndependentOrth.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LinearIndependentOrth.lean#L15-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinearIndependentOrth
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

theorem Formalism.L2.SG.Pf.GluingBases.locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by sorry
