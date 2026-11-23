-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_latFinite
-- name    : Formalism.LatticeIndexTer.latFinite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:38.346352+00:00
-- url     : https://prove2.me/theorems/ef390ba9-9b4b-4d11-b4fd-498b8332bdb9
-- title:
--   Lattice Index Ter: lat Finite
-- statement:
--   The Lattice Index Ter construction uses the lat Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/LogProductFormula.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/LogProductFormula.lean#L10-L10

import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeIndexTer

theorem Formalism.LatticeIndexTer.latFinite : LatFinite := by sorry
