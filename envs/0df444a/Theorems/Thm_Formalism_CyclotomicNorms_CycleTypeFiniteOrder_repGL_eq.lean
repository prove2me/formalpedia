-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL_eq
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:25.573482+00:00
-- url     : https://prove2.me/theorems/52ce25a2-6570-4e53-8825-6ca487eedf8e
-- title:
--   Cycle Type Finite Order: rep GL eq
-- statement:
--   The Cycle Type Finite Order construction uses the rep GL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L402-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L402-L402

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_eq (A : GL (Fin N) K) : repGL A = Matrix.toLin' (A : Matrix (Fin N) (Fin N) K) := by sorry
