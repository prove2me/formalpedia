-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_euler_monomial
-- name    : Formalism.L2.G.Model.sw_euler_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.035074+00:00
-- url     : https://prove2.me/theorems/bc35a4b0-e4fa-42e3-afad-2f6bfb77289f
-- title:
--   Model: sw euler monomial
-- statement:
--   The Model construction uses the sw euler monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L106-L110

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
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

theorem Formalism.L2.G.Model.sw_euler_monomial (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowDiv R a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) • monomial m c := by sorry
