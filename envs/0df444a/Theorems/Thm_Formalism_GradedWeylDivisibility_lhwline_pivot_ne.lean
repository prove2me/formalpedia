-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_pivot_ne
-- name    : Formalism.GradedWeylDivisibility.lhwline_pivot_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:46.663319+00:00
-- url     : https://prove2.me/theorems/09c25219-1f85-4ed8-8c62-94ec2c93bd1e
-- title:
--   Graded Weyl Divisibility: lhwline pivot ne
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline pivot ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L223-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L223-L239

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_pivot_ne (k : ℕ) (hr : k + 1 ≤ r) (hn : k + 1 ≤ n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hd : eval y (lpMinor K (k + 1) hr hn) ≠ 0) :
    y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0 := by sorry
