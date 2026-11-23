-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_pairs_nat
-- name    : Formalism.DegreeFormula.PFlagDeg.pairs_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:18.361462+00:00
-- url     : https://prove2.me/theorems/ad0ea5a1-20fa-4b8e-818b-2feea7d2aaa6
-- title:
--   PFlag Deg: pairs nat
-- statement:
--   The PFlag Deg construction uses the pairs nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L138-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L138-L161

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg

theorem Formalism.DegreeFormula.PFlagDeg.pairs_nat (N : ℕ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (sfac N : ℝ) := by sorry
