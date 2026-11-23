-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_sum_delta
-- name    : Formalism.DegreeFormula.PermutationPointDegree.sum_delta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:46.266028+00:00
-- url     : https://prove2.me/theorems/7734d559-68cf-4ae7-af4f-252af2775431
-- title:
--   Permutation Point Degree: sum delta
-- statement:
--   The Permutation Point Degree construction uses the sum delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L18-L24

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula

theorem Formalism.DegreeFormula.PermutationPointDegree.sum_delta (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by sorry
