-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_mem_of_span
-- name    : Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:29.594296+00:00
-- url     : https://prove2.me/theorems/b1192834-93b3-4951-a860-a1030fa4ebf9
-- title:
--   Lattice Index Length: exists smul mem of span
-- statement:
--   The Lattice Index Length construction uses the exists smul mem of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L81-L83

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]

theorem Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (B : Submodule O X) (hB : Submodule.span K (B : Set X) = ⊤)
    (x : X) : ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by sorry
