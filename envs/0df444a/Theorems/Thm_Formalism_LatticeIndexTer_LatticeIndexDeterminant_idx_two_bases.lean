-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idx_two_bases
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.idx_two_bases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:25.39101+00:00
-- url     : https://prove2.me/theorems/838d114e-c446-4d4e-82b2-2bd37cea3b98
-- title:
--   Lattice Index Determinant: idx two bases
-- statement:
--   The Lattice Index Determinant construction uses the idx two bases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L134-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L134-L200

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

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.idx_two_bases (b b' : Basis ι K Y) (a c0 : O) (ha : a ≠ 0) (hc0 : c0 ≠ 0)
    (h : algebraMap O K a = (b.toMatrix b').det * algebraMap O K c0) :
    idx O Y (Submodule.span O (Set.range b)) (Submodule.span O (Set.range b')) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O c0).toNat : ℤ) := by sorry
