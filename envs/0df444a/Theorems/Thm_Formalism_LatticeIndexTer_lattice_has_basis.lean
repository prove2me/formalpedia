-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_lattice_has_basis
-- name    : Formalism.LatticeIndexTer.lattice_has_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:03.75981+00:00
-- url     : https://prove2.me/theorems/8f39cf7e-bd42-4eb0-b46b-238a7fa809aa
-- title:
--   Lattice Index Ter: lattice has basis
-- statement:
--   The Lattice Index Ter construction uses the lattice has basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L173-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L173-L186

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

theorem Formalism.LatticeIndexTer.lattice_has_basis : LatBasis := by sorry
