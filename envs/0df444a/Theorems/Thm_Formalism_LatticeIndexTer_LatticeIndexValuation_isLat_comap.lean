-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexValuation_isLat_comap
-- name    : Formalism.LatticeIndexTer.LatticeIndexValuation.isLat_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:00.343804+00:00
-- url     : https://prove2.me/theorems/f8659720-6a71-4fdc-a439-9aa544c05cde
-- title:
--   Lattice Index Valuation: is Lat comap
-- statement:
--   The Lattice Index Valuation construction uses the is Lat comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndexSigned.lean#L48-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndexSigned.lean#L48-L70

import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexValuation
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem Formalism.LatticeIndexTer.LatticeIndexValuation.isLat_comap (A : Submodule O X) (hA : IsLat O K X A) (W : Submodule K X) :
    IsLat O K W (A.comap ((W.subtype).restrictScalars O)) := by sorry
