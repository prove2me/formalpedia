-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexValuation_length_map_inj
-- name    : Formalism.LatticeIndexTer.LatticeIndexValuation.length_map_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:37.234781+00:00
-- url     : https://prove2.me/theorems/20507eea-9005-4bfa-aebf-8589269097fc
-- title:
--   Lattice Index Valuation: length map inj
-- statement:
--   The Lattice Index Valuation construction uses the length map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndexSigned.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndexSigned.lean#L13-L36

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

theorem Formalism.LatticeIndexTer.LatticeIndexValuation.length_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Module.length O (P ⧸ Q.comap P.subtype) =
      Module.length O (P.map ι ⧸ (Q.map ι).comap (P.map ι).subtype) := by sorry
