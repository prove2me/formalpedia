-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NormUnitsOrthogonality_det_unit_of_selfdual
-- name    : Formalism.L2.SG.Pf.NormUnitsOrthogonality.det_unit_of_selfdual
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:14.941816+00:00
-- url     : https://prove2.me/theorems/601af63c-b036-4d4c-9e90-28c6e7a1be5e
-- title:
--   Norm Units Orthogonality: det unit of selfdual
-- statement:
--   The Norm Units Orthogonality construction uses the det unit of selfdual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DetUnitOfSelfdual.lean#L65-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DetUnitOfSelfdual.lean#L65-L101

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det

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

theorem Formalism.L2.SG.Pf.NormUnitsOrthogonality.det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by sorry
