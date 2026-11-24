-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_index_scalar_multiple_eq
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.index_scalar_multiple_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:29.032053+00:00
-- url     : https://prove2.me/theorems/5c5c85d8-1c46-48a2-ab96-8680edcf51c3
-- title:
--   Lattice Index Determinant: index scalar multiple eq
-- statement:
--   The Lattice Index Determinant construction uses the index scalar multiple eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L247-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L247-L261

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
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.index_scalar_multiple_eq {X ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module K X]
    [Module O X] [IsScalarTower O K X] (bN : Basis ι K X) (u : K) (hu : u ≠ 0) (a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : algebraMap O K a = u ^ Fintype.card ι * algebraMap O K b) :
    idx O X (Submodule.span O (Set.range bN))
        ((Submodule.span O (Set.range bN)).map ((u • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by sorry
