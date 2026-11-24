-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_goodIndex_of_latFinite
-- name    : Formalism.LatticeIndexTer.goodIndex_of_latFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:20.737449+00:00
-- url     : https://prove2.me/theorems/7739e675-1734-4096-9aae-8ca413e47ca8
-- title:
--   Lattice Index Ter: good Index of lat Finite
-- statement:
--   The Lattice Index Ter construction uses the good Index of lat Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndex.lean#L187-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndex.lean#L187-L216

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Formalism.LatticeIndexTer.subgroupData

theorem Formalism.LatticeIndexTer.goodIndex_of_latFinite (h1 : LatFinite) : GoodIndex := by sorry
