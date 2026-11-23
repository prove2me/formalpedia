-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ndEv_colAddGen
-- name    : Formalism.GradedWeylDivisibility.ndEv_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:22.996508+00:00
-- url     : https://prove2.me/theorems/8feee649-cf80-4140-9db4-50b67fdc6af3
-- title:
--   Graded Weyl Divisibility: nd Ev col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the nd Ev col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L18-L25

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
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
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.ndEv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (colAddGen R l j g) = g := by sorry
