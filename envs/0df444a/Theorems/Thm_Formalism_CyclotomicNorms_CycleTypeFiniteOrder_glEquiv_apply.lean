-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv_apply
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.glEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:01.160793+00:00
-- url     : https://prove2.me/theorems/6f83c274-7679-4100-a2b6-b54ea2ec8fa9
-- title:
--   Cycle Type Finite Order: gl Equiv apply
-- statement:
--   The Cycle Type Finite Order construction uses the gl Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L423-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L423-L423

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {K : Type*} [Field K] {N : ℕ}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.glEquiv_apply (A : GL (Fin N) K) (x : Fin N → K) : glEquiv A x = repGL A x := by sorry
