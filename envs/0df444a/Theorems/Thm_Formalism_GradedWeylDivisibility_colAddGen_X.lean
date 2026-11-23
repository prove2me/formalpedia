-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_colAddGen_X
-- name    : Formalism.GradedWeylDivisibility.colAddGen_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.968807+00:00
-- url     : https://prove2.me/theorems/dfbc2892-63cf-4cff-9a43-954691953da1
-- title:
--   Graded Weyl Divisibility: col Add Gen X
-- statement:
--   The Graded Weyl Divisibility construction uses the col Add Gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L57-L60

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
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

theorem Formalism.GradedWeylDivisibility.colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by sorry
