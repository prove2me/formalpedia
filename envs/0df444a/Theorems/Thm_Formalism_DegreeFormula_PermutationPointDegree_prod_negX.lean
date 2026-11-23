-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_prod_negX
-- name    : Formalism.DegreeFormula.PermutationPointDegree.prod_negX
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:48.707799+00:00
-- url     : https://prove2.me/theorems/3feb966f-185d-49e3-adec-a3944f816e7e
-- title:
--   Permutation Point Degree: prod neg X
-- statement:
--   The Permutation Point Degree construction uses the prod neg X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L26-L32

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

theorem Formalism.DegreeFormula.PermutationPointDegree.prod_negX {ι : Type} [Fintype ι] {N : ℕ} (e : ι × Fin N → ℕ) :
    (∏ x : ι × Fin N, (-X x : MvPolynomial (ι × Fin N) ℝ) ^ (e x)) =
      C ((-1 : ℝ) ^ (∑ x, e x)) * monomial (Finsupp.equivFunOnFinite.symm e) 1 := by sorry
