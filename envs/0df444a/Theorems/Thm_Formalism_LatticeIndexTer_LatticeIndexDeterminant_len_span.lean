-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_len_span
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:39.200393+00:00
-- url     : https://prove2.me/theorems/70093c2a-33e3-441b-bda9-338bd87929e1
-- title:
--   Lattice Index Determinant: len span
-- statement:
--   The Lattice Index Determinant construction uses the len span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L80-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L80-L132

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

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span (b : Basis ι K Y) (w : ι → Y) (hw : ∀ j, w j ∈ Submodule.span O (Set.range b))
    (hdet : (b.toMatrix w).det ≠ 0) :
    ∃ e : O, algebraMap O K e = (b.toMatrix w).det ∧
      Module.length O (Submodule.span O (Set.range b) ⧸
        (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype) =
        IsDiscreteValuationRing.addVal O e := by sorry
