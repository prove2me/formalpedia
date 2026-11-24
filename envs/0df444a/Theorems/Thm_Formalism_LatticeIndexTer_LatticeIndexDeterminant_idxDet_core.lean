-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idxDet_core
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.idxDet_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:38.12741+00:00
-- url     : https://prove2.me/theorems/7f8e9b6a-55b5-4284-9986-16980181f918
-- title:
--   Lattice Index Determinant: idx Det core
-- statement:
--   The Lattice Index Determinant construction uses the idx Det core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L202-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L202-L218

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.idxDet_core {X : Type} [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b) :
    idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by sorry
