-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_lattice_quotient_finite
-- name    : Formalism.LatticeIndexTer.lattice_quotient_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:23.847678+00:00
-- url     : https://prove2.me/theorems/7f2185ec-8094-4044-bf41-2afe1216cc8c
-- title:
--   Lattice Index Ter: lattice quotient finite
-- statement:
--   The Lattice Index Ter construction uses the lattice quotient finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L154-L157

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
open LatticeIndexLength

theorem Formalism.LatticeIndexTer.lattice_quotient_finite : LatFinite := by sorry
