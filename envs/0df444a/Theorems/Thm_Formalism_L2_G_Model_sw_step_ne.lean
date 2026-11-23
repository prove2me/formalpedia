-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_step_ne
-- name    : Formalism.L2.G.Model.sw_step_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:38.098857+00:00
-- url     : https://prove2.me/theorems/fd459c47-a82f-401f-bd2e-23b9fd6b8bd2
-- title:
--   Model: sw step ne
-- statement:
--   The Model construction uses the sw step ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L62-L69

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}

theorem Formalism.L2.G.Model.sw_step_ne (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a b (k + 1) f = rowDiv R a b k (Dop R a b f) := by sorry
