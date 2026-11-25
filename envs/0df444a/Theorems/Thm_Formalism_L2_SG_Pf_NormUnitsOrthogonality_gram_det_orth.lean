-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NormUnitsOrthogonality_gram_det_orth
-- name    : Formalism.L2.SG.Pf.NormUnitsOrthogonality.gram_det_orth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:15:33.921951+00:00
-- url     : https://prove2.me/theorems/0fad4e98-81ba-4d8c-8b05-74606330ebbf
-- title:
--   Norm Units Orthogonality: gram det orth
-- statement:
--   The Norm Units Orthogonality construction uses the gram det orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DetUnitOfSelfdual.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DetUnitOfSelfdual.lean#L115-L122

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_gram_det_orth

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem Formalism.L2.SG.Pf.NormUnitsOrthogonality.gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by sorry
