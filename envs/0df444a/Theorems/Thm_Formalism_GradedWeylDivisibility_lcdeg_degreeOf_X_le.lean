-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcdeg_degreeOf_X_le
-- name    : Formalism.GradedWeylDivisibility.lcdeg_degreeOf_X_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:05.682869+00:00
-- url     : https://prove2.me/theorems/8af8f2fa-0094-4836-ac87-5a8d7572472e
-- title:
--   Graded Weyl Divisibility: lcdeg degree Of X le
-- statement:
--   The Graded Weyl Divisibility construction uses the lcdeg degree Of X le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCdegLemmas.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCdegLemmas.lean#L9-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCdegLemmas
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

theorem Formalism.GradedWeylDivisibility.lcdeg_degreeOf_X_le {σ R : Type*} [CommRing R] [DecidableEq σ] (i j : σ) :
    degreeOf i (X j : MvPolynomial σ R) ≤ if j = i then 1 else 0 := by sorry
