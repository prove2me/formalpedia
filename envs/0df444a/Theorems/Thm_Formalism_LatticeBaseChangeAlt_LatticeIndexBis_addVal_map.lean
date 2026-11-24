-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_addVal_map
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.addVal_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:10.395735+00:00
-- url     : https://prove2.me/theorems/f625dbe2-ae5d-4346-a0b7-0690105025b9
-- title:
--   Lattice Index Bis: add Val map
-- statement:
--   The Lattice Index Bis construction uses the add Val map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L150-L157

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.addVal_map {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O)
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ)) (x : O) (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal O' (algebraMap O O' x) = IsDiscreteValuationRing.addVal O x := by sorry
