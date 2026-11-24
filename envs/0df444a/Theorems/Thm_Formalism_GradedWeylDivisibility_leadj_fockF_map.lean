-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_fockF_map
-- name    : Formalism.GradedWeylDivisibility.leadj_fockF_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:38.862092+00:00
-- url     : https://prove2.me/theorems/2afc8ff6-15de-4aff-9049-3ad1e43ecf90
-- title:
--   Graded Weyl Divisibility: leadj fock F map
-- statement:
--   The Graded Weyl Divisibility construction uses the leadj fock F map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowAct.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowAct.lean#L12-L18

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.leadj_fockF_map {σ : Type*} (f g : MvPolynomial σ ℚ) :
    fockF (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = ((fockQ f g : ℚ) : ℂ) := by sorry
