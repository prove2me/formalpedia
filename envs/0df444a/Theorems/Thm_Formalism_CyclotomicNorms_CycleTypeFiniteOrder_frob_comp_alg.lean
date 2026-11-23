-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_frob_comp_alg
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.frob_comp_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:50.490326+00:00
-- url     : https://prove2.me/theorems/8ff2f871-3d30-4aaa-9d51-9b0aeab39e49
-- title:
--   Cycle Type Finite Order: frob comp alg
-- statement:
--   The Cycle Type Finite Order construction uses the frob comp alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L43-L44

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
variable {g : ℕ} [hg : Fact g.Prime]

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.frob_comp_alg : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) =
    algebraMap (ZMod g) (Fbar g) := by sorry
