-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_idx_map_inj
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.idx_map_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:51:58.200879+00:00
-- url     : https://prove2.me/theorems/0f58dc82-b24c-4152-b581-cc758eb73b15
-- title:
--   Lattice Index Bis: idx map inj
-- statement:
--   The Lattice Index Bis construction uses the idx map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L13-L38

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

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.idx_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Formalism.LatticeIndexTer.idx O X (P.map ι) (Q.map ι) = Formalism.LatticeIndexTer.idx O Y P Q := by sorry
