-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL_apply
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:39.397612+00:00
-- url     : https://prove2.me/theorems/c12130cc-e4d4-4a04-8ac3-3535809e59ad
-- title:
--   Cycle Type Finite Order: rep GL apply
-- statement:
--   The Cycle Type Finite Order construction uses the rep GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L404-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L404-L406

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_apply (A : GL (Fin N) K) (x : Fin N → K) :
    repGL A x = Matrix.mulVec (A : Matrix (Fin N) (Fin N) K) x := by sorry
